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
import State.{Counters, EmptyIdempotentInfo, IdempotentInfo, IdempotentStats}
import dotty.tools.dotc.core.Constants.Constant

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

  override def runsAfter =
    Set(classOf[ElimByName], classOf[IdempotencyInference])

  type Analyzer = (Tree, Tree, PREContext) => PREContext
  type PreOptimizer = () => Unit
  type Transformer = (Tree => Tree)
  type Optimization = (Context) => (Analyzer, PreOptimizer, Transformer)

  import collection.mutable.ListBuffer
  type Traversal = ListBuffer[List[IdempotentTree]]
  type PREContext = (State, Traversal)

  /** Represents the new declaration, assignation and reference. */
  type Optimized = (ValDef, Tree, Tree)

  def reportError(msg: String, tree: Tree)(implicit ctx: Context) = {
    ctx.error(s"$tree $msg", tree.pos); tree
  }

  override def transformDefDef(tree: tpd.DefDef)(
      implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val ctx0: Context = ctx.withModeBits(Mode.FutureDefsOK)
    val result = {
      implicit val ctx: Context = ctx0

      if (!tree.symbol.is(Flags.Label)) {
        val (analyzer, preOptimizer, transformer) =
          elimCommonSubexpression(ctx.withOwner(tree.symbol))
        val emptyTraversal = ListBuffer[List[IdempotentTree]]()
        analyzer(tree, tree, State() -> emptyTraversal)

        // Set up the optimization environment
        preOptimizer()

        val newTree = new TreeMap() {
          override def transform(tree: tpd.Tree)(implicit ctx: Context) =
            transformer(super.transform(tree))
        }.transform(tree)

        if (newTree ne tree)
          println(s"${tree.symbol} after $phaseName became ${newTree.show}")

        newTree match {
          case newDef: DefDef =>
            if (tree ne newDef) newDef
            else tree
          case _ => reportError("is expected to be a DefDef", newTree)
        }
      } else tree
    }

    result
  }

  def elimCommonSubexpression: Optimization = (ctx0: Context) => {
    implicit val ctx: Context = ctx0

    import collection.mutable

    /* Keep the parental relations between two gives scopes. */
    var outerScopes = mutable.HashMap[Tree, Tree]()

    /* Minimum depth in which a potential optimized tree has been found. */
    var minDepths = mutable.HashMap[IdempotentTree, Int]()

    /* DummyTrees that are introduced to know where the optimized `ValDef`s need
     * to be spliced when their wrappers are trees that don't have symbols. */
    var entrypoints = mutable.HashSet[Symbol]()

    /* Maps original trees to entrypoints that need to be spliced when found. */
    var needsEntrypoint = mutable.HashMap[Tree, Tree]()

    /* Contexts that store the PREContext for every method. */
    val orderedContexts = mutable.ListBuffer[(PREContext, Tree)]()

    /* Replace by trees that are either a init or a ref of an optimized valdef. */
    val replacements = mutable.HashMap[Tree, Tree]()

    /* Store the declarations of the optimized valdefs. */
    val declarations = mutable.HashMap[Symbol, List[ValDef]]()

    def analyzer(tree: Tree, topLevel: Tree, currentCtx: PREContext): PREContext = {
      tree match {
        case valDef: ValDef =>
          analyzer(valDef.rhs, topLevel, currentCtx)

        case defDef: DefDef =>
          if (tree == topLevel) {
            val (state, traversal) = analyzer(defDef.rhs, topLevel, currentCtx)
            val optimizedState = state.retainOptimizableExpressions
            val newContext = optimizedState -> traversal
            orderedContexts += (newContext -> tree)
            newContext
          } else currentCtx

        case block: Block =>
          (block.stats ::: List(block.expr)).foldLeft(currentCtx) {
            (context, subTree) => analyzer(subTree, topLevel, context)
          }

        case branch @ If(cond, thenp, elsep) =>
          val state = analyzer(cond, topLevel, currentCtx)
          val analyzed = List(thenp, elsep).map(analyzer(_, topLevel, state))
          analyzed.reduceLeft { (accContext, newContext) =>
            // Traversal list is mutable, choose whichever
            accContext._1.intersect(newContext._1) -> newContext._2
          }

        case tree: Tree =>
          IdempotentTrees.from(tree) match {
            case Some(idempotent) =>
              val allSubTrees = IdempotentTrees.allIdempotentTrees(idempotent)
              val (currentState, traversal) = currentCtx
              if (allSubTrees.nonEmpty) traversal += allSubTrees

              val newState = allSubTrees.foldLeft(currentState) { (state, st) =>
                val subTree = st.tree
                val (counters, stats) = state.get
                val currentCounter = counters.getOrElse(st, 0)
                val (inits, refs) = stats.getOrElse(st, EmptyIdempotentInfo)
                val newInits = if (currentCounter == 0) subTree :: inits else inits
                val newRefs = if (currentCounter == 0) refs else subTree :: refs
                val newCounters = counters + (st -> (currentCounter + 1))
                val newStats = stats + (st -> (newInits -> newRefs))
                State(newCounters -> newStats)
              }

              newState -> traversal

            case _ => currentCtx
          }

        case _ => currentCtx
      }
    }

    /* Register a `ValDef` to be introduced before the tree with the symbol. */
    @inline def registerValDef(target: ValDef, defn: Symbol) = {
      val otherTargets = declarations(defn)
      declarations += (defn -> (target :: otherTargets))
    }

    def generateEntrypoint: ValDef =
      tpd.SyntheticValDef(ctx.freshName("entrypoint$$").toTermName, EmptyTree)

    def registerEntrypoint(at: Tree): ValDef = {
      val entrypoint = generateEntrypoint
      val entrypointSymbol = entrypoint.symbol
      entrypoints += entrypointSymbol
      needsEntrypoint += at -> entrypoint
      declarations += (entrypointSymbol -> List.empty[ValDef])
      entrypoint
    }

    def pruneShorterTrees(counters: List[(IdempotentTree, Int)]) = {
      if (counters.isEmpty) Nil else {
        counters.foldLeft(List(counters.head)){ (acc, itreeCounter) =>
          val (parent, parentCounter) = acc.head
          val (itree, childCounter) = itreeCounter
          if (parentCounter == childCounter &&
              parent.tree.existsSubTree(_ == itree.tree)) acc
          else itreeCounter :: acc
        }.map(_._1)
      }
    }

    /** Return result of the optimization */
    @inline def optimize(cand: IdempotentTree): Optimized = {
      val name = ctx.freshName("cse$$").toTermName
      if (name.toString.contains("570"))
        println("dsds")
      val flags = Flags.Synthetic | Flags.Mutable
      val rhs = cand.tree
      val (tpe, pos) = (rhs.tpe.widen, rhs.pos)
      val symbol = ctx.newSymbol(ctx.owner, name, flags, tpe, coord = pos)
      val valDef = tpd.ValDef(symbol, tpd.defaultValue(tpe))
      val ref = tpd.ref(symbol)
      val valDefIdent = tpd.ref(symbol)
      val assign = tpd.Block(List(valDefIdent.becomes(rhs)), ref)
      (valDef, assign, ref)
    }


    val preOptimizer: PreOptimizer = () => {
      def optimizeContext(context: PREContext, host: Tree): Unit = {
        val hostSymbol = host.symbol
        val (state, traversal) = context
        val (counters, stats) = state.get
        val optimizedCache = mutable.HashSet[IdempotentTree]()

        traversal.foreach { forest =>
          val cs = forest.iterator.map(t => t -> counters.getOrElse(t, 0))
          val candidates = cs.filter(_._2 > 1).toList
          val pruned = pruneShorterTrees(candidates)

          pruned.foreach { itree =>
            if (!optimizedCache.contains(itree)) {
              val (declaration, assignation, reference) = optimize(itree)
              val (inits, refs) = stats(itree)
              val other = declarations.getOrElse(hostSymbol, List.empty[ValDef])
              val updatedDeclarations = declaration :: other
              declarations += hostSymbol -> updatedDeclarations
              inits.foreach(init => replacements += init -> assignation)
              refs.foreach(ref => replacements += ref -> reference)
              optimizedCache += itree
            }
          }
        }
      }

      orderedContexts.foreach(p => optimizeContext(p._1, p._2))
    }

    val transformer: Transformer = {
      case defDef: DefDef
        if declarations.contains(defDef.symbol) =>
        // Introduce new val defs for this enclosing tree
        val enclosingSym = defDef.symbol
        val optimizedValDefs = declarations(enclosingSym).reverse
        declarations -= enclosingSym

        if (optimizedValDefs.nonEmpty) {
          if (true)
            println(i"Introducing ${optimizedValDefs.map(_.show)}")
          val finalRhs = defDef.rhs match {
            case blk @ Block(stats, expr) =>
              cpy.Block(blk)(optimizedValDefs ::: stats, expr)
            case singleRhs =>
              tpd.Block(optimizedValDefs, singleRhs)
          }
          cpy.DefDef(defDef)(rhs = finalRhs.withType(finalRhs.tpe.widenIfUnstable))
        } else defDef

      case tree =>
        val resultingTree = replacements.get(tree) match {
          case Some(ref) => ref
          case None => tree
        }
        if (debug && (resultingTree ne tree))
          println(s"Rewriting ${tree.show} to ${resultingTree.show}")
        resultingTree
    }

    (analyzer _, preOptimizer, transformer)
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
    ctx.idempotencyPhase
      .asInstanceOf[IdempotencyInference]
      .invalidMethodRef(sym)

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
          val replacedArgs = args.map(loop)
          cpy.Apply(tree)(loop(fn), replacedArgs)
        case t => t
      }
    }
    IdempotentTrees(loop(itree.tree))
  }

}

object State {

  import tpd.Tree
  type Counters = Map[IdempotentTree, Int]
  type IdempotentInfo = (List[Tree], List[Tree])
  type IdempotentStats = Map[IdempotentTree, IdempotentInfo]

  val EmptyIdempotentInfo = (List.empty[Tree], List.empty[Tree])

  def apply(): State = State(
    Map[IdempotentTree, Int]() -> Map[IdempotentTree, IdempotentInfo]()
  )

}

case class State(get: (Counters, IdempotentStats)) extends AnyVal {

  def intersect(other: State): State = {
    val (cs, stats) = get
    val (cs2, stats2) = other.get

    var newCounters = Map[IdempotentTree, Int]()
    cs.foreach { pair =>
      val (key, value) = pair
      cs2.get(key) match {
        case Some(value2) =>
          newCounters = newCounters + (key -> (value + value2))
        case None => key -> 0
      }
    }

    var newInfo = Map[IdempotentTree, IdempotentInfo]()
    stats.foreach { pair =>
      val (key, value) = pair
      stats2.get(key) match {
        case Some(value2) =>
          val mixedInits = value._1 ++ value2._1
          val mixedRefs = value._2 ++ value2._2
          newInfo = newInfo + (key -> (mixedInits -> mixedRefs))
        case None =>
      }
    }

    State(newCounters -> newInfo)
  }

  def retainOptimizableExpressions: State = {
    val optimizable = get._1.filter(_._2 > 1)
    val optimizableStats = get._2.filterKeys(optimizable.contains)
    State(optimizable -> optimizableStats)
  }

  override def toString =
    s"===\nCOUNTERS (${get._1.size}) :\n${get._1.mkString("\n")}" +
      s"\n\nSTATS (${get._2.size}) :\n${get._2.mkString("\n")}\n===\n"

}

