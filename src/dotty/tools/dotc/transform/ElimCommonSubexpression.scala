package dotty.tools.dotc
package transform

import TreeTransforms._
import core._
import Symbols._
import Contexts._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.transform.IdempotentTrees.IdempotentTree
import dotty.tools.dotc.transform.linker.IdempotencyInference

import scala.annotation.tailrec

/** This phase performs Common Subexpression Elimination (CSE) that
  * precomputes an expression into a new variable when it's used
  * several times within the same scope.
  *
  * This optimization is applied for either vals, lazy vals or
  * expressions annotated with `Idempotent`. Such annotation is used to
  * ensure to the compiler that a concrete expression has no side effects.
  *
  * For instance, the following code:
  * {{{
  *   val a = 1
  *   val b = a + a + 2
  *   val c = a + a + 4
  * }}}
  *
  * will be transformed to:
  * {{{
  *   val a = 1
  *   val a1 = a + a
  *   val b = a1 + 2
  *   val c = a1 + 2
  * }}}
  *
  * only if `+` is guaranteed to be idempotent.
  *
  * @author jvican (Inspired by the work of @allanrenucci)
  *
  */
class ElimCommonSubexpression extends MiniPhaseTransform {

  import ast._
  import ast.tpd._
  import Decorators._

  override def phaseName = "elimCommonSubexpression"

  private final val debug = false

  override def runsAfter = Set(classOf[ElimByName], classOf[IdempotencyInference])

  /* Imitate `Simplify` structure for the moment being */
  type Visitor = Tree => Unit
  val NoVisitor: Visitor = (_) => ()
  type Transformer = () => (Tree => Tree)
  type Optimization = (Context) => (String, Visitor, Transformer)

  /** Performs CSE only **once** and does not repeat the transformation.
    * If you add a `while` check that the transformation is first idempotent,
    * in the true meaning of the word. Otherwise, infinite cycles may happen. */
  override def transformDefDef(tree: tpd.DefDef)(
      implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val ctx0: Context = ctx.withModeBits(Mode.FutureDefsOK)
    val result = {
      implicit val ctx: Context = ctx0
      if (!tree.symbol.is(Flags.Label)) {
        var rhs0 = tree.rhs
        val (name, nextVisitor, nextTransformer) = elimCommonSubexpression(
          ctx.withOwner(tree.symbol))
        rhs0.foreachSubTree(nextVisitor)
        val transformer = nextTransformer()
        val rhst = new TreeMap() {
          override def transform(
                                  tree: tpd.Tree)(implicit ctx: Context): tpd.Tree =
            transformer(super.transform(tree))
        }.transform(rhs0)
        if (rhst ne rhs0)
          println(s"${tree.symbol} after $name became ${rhst.show}")
        rhs0 = rhst
        if (rhs0 ne tree.rhs) cpy.DefDef(tree)(rhs = rhs0)
        else tree
      } else tree
    }
    result
  }

  /** Lifted up val def and tree referencing to it */
  type Optimized = (ValDef, Tree)
  sealed trait Position
  case object OutsideDef extends Position
  case object InsideDef extends Position
  type OptimizedValDef = (ValDef, Position)

  def elimCommonSubexpression: Optimization = (ctx0: Context) => {
    implicit val ctx: Context = ctx0

    import collection.mutable

    /* Map symbols of ValDef or DefDef to the new ValDefs they depend on */
    val hostsOfOptimizations = mutable.HashMap[Symbol, List[ValDef]]()

    var outerScopes = mutable.HashMap[Tree, Tree]()
    var depths = mutable.HashMap[Tree, Int]()
    var minDepths = mutable.HashMap[IdempotentTree, Int]()

    /* Trees that have already been analyzed by the analyzer */
    var analyzed = mutable.HashSet[Tree]()

    /* Keep track of the order in which the analyzer visits trees */
    var orderExploration = mutable.ListBuffer[Tree]()

    /* Idempotent trees are expensive to build, cache to reuse them*/
    var cached = mutable.HashMap[Tree, List[IdempotentTree]]()

    /* Keep track of the number of appearances of every idempotent tree. */
    var appearances = mutable.HashMap[IdempotentTree, Int]()

    /* Store necessary information to optimize these idempotent trees. */
    val optimized = mutable.HashMap[IdempotentTree, Optimized]()

    /* Map normal trees to the unique idempotent instance that represents them. */
    val toSubstitute = mutable.HashMap[Tree, IdempotentTree]()

    /* Map an idempotent tree to all the trees that have the same representation. */
    var subscribedTargets = mutable.HashMap[IdempotentTree, mutable.Set[Tree]]()

    def emptyMutableSet = collection.mutable.HashSet[Tree]()

    @inline def updateMinDepth(itree: IdempotentTree, depth: Int) =
      minDepths += (itree -> Math.min(minDepths.getOrElse(itree, 0), depth))

    def analyzer(t: Tree, depth: Int): Boolean = t match {
      case valDefDef: ValOrDefDef =>
        analyzed += valDefDef
        val rhs = valDefDef.rhs

        val foundIdempotent = analyzer(rhs, depth + 1)
        if (foundIdempotent) {
          outerScopes += (rhs -> valDefDef)
          hostsOfOptimizations += (valDefDef.symbol -> List.empty[ValDef])
        }
        foundIdempotent

      case block: Block =>
        var foundIdempotent = false

        (block.expr :: block.stats).foreach { st =>
          val hasIdempotent = analyzer(st, depth + 1)
          foundIdempotent |= hasIdempotent
          if (hasIdempotent) outerScopes += (st -> block)
        }

        if (foundIdempotent)
          hostsOfOptimizations += (block.symbol -> List.empty[ValDef])
        foundIdempotent

      case tree: Tree if !analyzed.contains(tree) =>
        IdempotentTrees.from(tree) match {
          case Some(idempotent) =>
            if (debug) println(s"PROCESSING IS: $tree")
            val allSubTrees = IdempotentTrees.allIdempotentTrees(idempotent)
            tree.foreachSubTree(st => analyzed += st)
            if (allSubTrees.nonEmpty) {
              cached += tree -> allSubTrees
              orderExploration += tree
              depths += (tree -> depth)
              updateMinDepth(idempotent, depth)
              allSubTrees.foreach { st =>
                val subTree = st.tree
                if (debug) println(s"SUB TREE IS: $subTree")
                analyzed += subTree
                val current = appearances.getOrElse(st, 0)
                appearances += st -> (current + 1)
                // Subscribe all the trees interested in the optimization for idem
                val targets = subscribedTargets.getOrElse(st, emptyMutableSet)
                subscribedTargets += (st -> (targets += st.tree))
              }
            }
            true

          case _ => false
        }

      case _ => false
    }

    val visitor: Visitor = {
      case valDefDef: ValOrDefDef if !analyzed.contains(valDefDef) =>
        // Optimizing within blocks for the moment
        analyzer(valDefDef, 0)

      case t =>
    }

    val transformer: Transformer = () => {
      val topLevelIdempotentParents = mutable.ListBuffer.empty[IdempotentTree]
      val orderedCandidates = orderExploration.iterator.map(cached.apply)
      val candidatesBatches = orderedCandidates.map(itrees => {
        if (debug) println(s"ITREES: ${itrees.map(t => t -> appearances(t)).mkString("\n")}")
        topLevelIdempotentParents += itrees.head
        val cs = itrees.iterator
          .map(itree => itree -> appearances(itree))
          .filter(_._2 > 1).toList
        if (debug) println(s"CS: ${cs.mkString("\n")}")
        if (cs.nonEmpty) {
          // Make sure to optimize the longest common subexpression
          cs.tail.foldLeft(List(cs.head)) { (parents, child) => {
            val parent = parents.head
            /* Don't assume that traversing the list gives you the
             * idempotent trees in infix order (outside to the inside). */
            val sameSymbols = child._1.tree.symbol == parent._1.tree.symbol
            if (sameSymbols && child._2 == parent._2) parents
            else child :: parents
          }}
        } else cs
      }).toList
      if (debug) println(s"CANDBAT: ${candidatesBatches.mkString("\n")}")

      /* Perform optimization, add to optimized and return `ValDef` */
      @inline def optimize(cand: IdempotentTree): ValDef = {
        val termName = ctx.freshName("cse$$").toTermName
        val valDef = tpd.SyntheticValDef(termName, cand.tree)
        val ref = tpd.ref(valDef.symbol)
        optimized += (cand -> (valDef -> ref))
        valDef
      }

      /* Register optimization for all the interested original trees */
      @inline def prepareTargets(previousCand: IdempotentTree,
                                 cand: IdempotentTree) = {
        val prevTree = previousCand.tree
        subscribedTargets.get(previousCand) match {
          case Some(allTargets) =>
            allTargets foreach { t =>
              val t2 = if (t == prevTree) cand.tree else t
              toSubstitute += (t2 -> cand)
            }
          case None =>
        }
      }

      /* Register a `ValDef` to be introduced before the tree with the symbol. */
      @inline def registerValDef(target: ValDef, defn: Symbol) = {
        val otherTargets = hostsOfOptimizations(defn)
        hostsOfOptimizations += (defn -> (target :: otherTargets))
      }

      @tailrec def getEnclosingTree(tree: Tree, depth: Int): Tree = {
        if (depth == 0) tree
        else getEnclosingTree(outerScopes(tree), depth - 1)
      }

      val candidatesWithParents =
        (candidatesBatches zip topLevelIdempotentParents).filter(_._1.nonEmpty)

      candidatesWithParents.foreach { pair =>
        val (itrees, parent) = pair
        val onlyTrees = itrees.map(_._1)
        val firstChild = onlyTrees.head

        if (!optimized.contains(firstChild)) {
          val seenDepth = depths(parent.tree)
          val minDepth = minDepths(parent)
          val enclosingTree = getEnclosingTree(parent.tree, seenDepth - minDepth)
          val target = enclosingTree.symbol

          val firstValDef = optimize(firstChild)
          prepareTargets(firstChild, firstChild)
          registerValDef(firstValDef, target)

          onlyTrees.tail.foldLeft(firstChild) { (optimizedChild, itree) =>
            val (_, ref) = optimized(optimizedChild)
            val replaced = IdempotentTrees.replace(itree, optimizedChild, ref)
            if (!optimized.contains(replaced)) {
              val valDef = optimize(replaced)
              prepareTargets(itree, replaced)
              registerValDef(valDef, target)
              replaced
            } else replaced
          }
        }
      }

      // Free up unnecessary memory
      appearances = null
      subscribedTargets = null
      analyzed = null
      outerScopes = null
      depths = null
      minDepths = null
      cached = null

      def changeReference(idem: IdempotentTree, original: Tree): Tree = {
        optimized.get(idem) match {
          case Some((vdef, ref)) => ref
          case None => original
        }
      }

      val transformation: Tree => Tree = {
        case enclosingTree: ValOrDefDef
          if hostsOfOptimizations.contains(enclosingTree.symbol) =>

          // Introduce new val defs for this enclosing tree
          val optimizedValDefs = hostsOfOptimizations(enclosingTree.symbol).reverse
          hostsOfOptimizations -= enclosingTree.symbol
          if (optimizedValDefs.nonEmpty) {
            if (debug) println(s"introducing ${optimizedValDefs.map(_.show)}")
            enclosingTree match {
              case defDef: DefDef => // Place them inside rhs
                val finalRhs = defDef.rhs match {
                  case blk @ Block(stats, expr) =>
                    cpy.Block(blk)(optimizedValDefs ::: stats, expr)
                  case whatever =>
                    tpd.Block(optimizedValDefs, whatever)
                }
                cpy.DefDef(defDef)(rhs = finalRhs)
              case valDef: ValDef => // Place them on top of its definition
                tpd.Thicket(optimizedValDefs ::: List(enclosingTree))
            }
          } else enclosingTree

        case tree =>
          toSubstitute.get(tree) match {
            case Some(itree) => changeReference(itree, tree)
            case None =>
              /* We need to check if it's idempotent again because sub trees
               * may have changed/optimized and tree equality doesn't hold */
              IdempotentTrees.from(tree) match {
                case Some(itree) =>
                  val ret = changeReference(itree, tree)
                  if (debug && (ret ne tree))
                    println(s"rewriting ${tree.show} to ${ret.show}")
                  ret
                case None => tree
              }
          }
      }
      transformation
    }

    ("elimCommonSubexpression", visitor, transformer)
  }
}

object IdempotentTrees {

  import ast.tpd._

  class IdempotentTree(val tree: tpd.Tree)(implicit ctx: Context) {

    import scala.util.hashing.MurmurHash3.{seqHash, mix}

    /** Witness of structural equality by inspecting the tree */
    def idempotentHashCode(t: Tree)(implicit ctx: Context): Int = {
      t match {
        case EmptyTree => EmptyTree.hashCode()
        case _: This => t.symbol.hashCode()
        case _: Super => t.symbol.hashCode()
        case _: Ident => t.symbol.hashCode()
        case Literal(constant) =>
          if (constant.value == null) 0 else constant.value.hashCode()
        case Select(qual, name) =>
          mix(name.hashCode(), idempotentHashCode(qual))
        case Apply(fun1, args1) =>
          val idempotents = seqHash(args1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        case TypeApply(fun1, targs1) =>
          val idempotents = seqHash(targs1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        case _ => 0 // impossible case
      }
    }

    override def hashCode(): Int = idempotentHashCode(this.tree)

    /** Compare idempotent trees by structural equality */
    override def equals(that: Any): Boolean = that match {
      case thatIdempotent: IdempotentTree =>
        this.hashCode() == thatIdempotent.hashCode()
      case _ => false
    }

    override def toString = this.tree.toString
  }

  import ast.tpd._

  // Never call directly without having checked that it's indeed idempotent
  private def apply(tree: Tree)(implicit ctx: Context): IdempotentTree =
    new IdempotentTree(tree)

  def from(tree: Tree)(implicit ctx: Context): Option[IdempotentTree] =
    if (isIdempotent(tree)) Some(new IdempotentTree(tree)) else None

  def invalidMethodRef(sym: Symbol)(implicit ctx: Context): Boolean =
    ctx.idempotencyPhase.asInstanceOf[IdempotencyInference].invalidMethodRef(sym)

  def isIdempotent(tree: Tree)(implicit ctx: Context): Boolean =
    ctx.idempotencyPhase.asInstanceOf[IdempotencyInference].isIdempotent(tree)

  /** Collects all the valid idempotent sub trees, including the original tree.
    * NOTE: If you modify it, change also the semantics of `isIdempotent`. */
  def allIdempotentTrees(t1: IdempotentTree)(
      implicit ctx: Context): List[IdempotentTree] = {
    def collectValid(tree: Tree,
                     canBranch: Boolean = false): List[IdempotentTree] = {
      tree match {
        case Ident(_) | Literal(_) | This(_) | EmptyTree => Nil

        case Super(_, _) =>
          if (!canBranch) List(IdempotentTrees(tree)) else Nil

        case Select(qual, _) =>
          if (invalidMethodRef(tree.symbol)) {
            // Select may wrap other instances of Apply
            if (!canBranch) collectValid(qual, canBranch = true) else Nil
          } else IdempotentTrees(tree) :: collectValid(qual, canBranch = true)

        case TypeApply(fn, _) =>
          if (canBranch) {
            if (invalidMethodRef(fn.symbol)) Nil
            else IdempotentTrees(tree) :: collectValid(fn, canBranch = false)
          } else collectValid(fn)

        case Apply(fn, args) =>
          val collected = collectValid(fn, canBranch = false)
          val prefix =
            if (canBranch) IdempotentTrees(tree) :: collected else collected
          val cargs = args.map(a => collectValid(a, canBranch = true))
          val branched = if (cargs.nonEmpty) cargs.reduce(_ ++ _) else Nil
          prefix ::: branched

        case _ => Nil // Impossible case, tree must be non idempotent
      }
    }
    collectValid(t1.tree, canBranch = true)
  }

  /** Replace a targeted **idempotent** subtree by a reference to another new tree.
    * Only use this utility with trees that are known to be Idempotent. */
  def replace(itree: IdempotentTree, target: IdempotentTree, ref: Tree)(
      implicit ctx: Context): IdempotentTree = {
    def loop(tree: Tree)(implicit ctx: Context): Tree = {
      tree match {
        case _: Tree if tree == target.tree => ref
        case Select(qual, name) => cpy.Select(tree)(loop(qual), name)
        case TypeApply(fn, targs) => cpy.TypeApply(tree)(loop(fn), targs)
        case Apply(fn, args) =>
          val replacedArgs = args.map(loop(_))
          cpy.Apply(tree)(loop(fn), replacedArgs)
        case t => t
      }
    }
    IdempotentTrees(loop(itree.tree))
  }

}

