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
  private var optimizedTimes = 0

  override def runsAfter =
    Set(classOf[ElimByName], classOf[IdempotencyInference])

  type Analyzer = (Tree, Tree, PREContext) => PREContext
  type PreOptimizer = () => (Tree => Tree)
  type Transformer = (Tree => Tree)
  type Optimization = (Context) => (Analyzer, PreOptimizer, Transformer)

  import collection.mutable.ListBuffer
  type Traversal = ListBuffer[List[IdempotentTree]]
  type PREContext = (State, Traversal)

  /** Represents the new declaration, assignation and reference. */
  type Optimized = (ValDef, Assign, Tree)

  def reportError(msg: String, tree: Tree)(implicit ctx: Context) = {
    ctx.error(s"$tree $msg", tree.pos); tree
  }

  override def transformDefDef(tree: tpd.DefDef)(
      implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val ctx0: Context = ctx.withModeBits(Mode.FutureDefsOK)
    val result = {
      implicit val ctx: Context = ctx0

      if (!tree.symbol.is(Flags.Label)) {
        val (analyzer, nextOptimizer, transformer) =
          elimCommonSubexpression(ctx.withOwner(tree.symbol))
        val emptyTraversal = ListBuffer[List[IdempotentTree]]()
        analyzer(tree, tree, State() -> emptyTraversal)

        // Preoptimizer introduces entrypoints of valdefs
        val preOptimizer = nextOptimizer()
        val preOptimizedTree = new TreeMap() {
          override def transform(tree: tpd.Tree)(implicit ctx: Context) =
            preOptimizer(super.transform(tree))
        }.transform(tree)

        val newTree = new TreeMap() {
          override def transform(tree: tpd.Tree)(implicit ctx: Context) =
            transformer(super.transform(tree))
        }.transform(preOptimizedTree)

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

    /* DummyTrees that are introduced to know where the optimized `ValDef`s need
     * to be spliced when their wrappers are trees that don't have symbols. */
    var entrypoints = mutable.HashSet[Symbol]()

    /* Contexts that store the PREContext for every method. */
    val orderedContexts = mutable.ListBuffer[(PREContext, Tree)]()

    /* Replace by trees that are either a init or a ref of an optimized valdef. */
    val replacements = mutable.HashMap[Tree, Tree]()

    /* Store the declarations of the optimized valdefs. */
    val declarations = mutable.HashMap[Symbol, List[ValDef]]()

    /* Store the assignation of the optimized valdefs. */
    val assignations = mutable.HashMap[Symbol, List[Tree]]()

    trait EntrypointPosition
    case object InsideTreeAsTopLevel extends EntrypointPosition
    case object InsideBlock extends EntrypointPosition

    type EntrypointInfo = (Tree, EntrypointPosition)

    /* Maps original trees to entrypoints that need to be spliced when found. */
    var needsEntrypoint = mutable.HashMap[Tree, EntrypointInfo]()

    def isUnitConstant(tree: Tree) = tree match {
      case Literal(constant) => constant == Constant(())
      case _ => false
    }

    def getFirstInnerTree(from: Tree) = from match {
      case Block(stats2, expr) =>
        if (stats2.isEmpty) expr else stats2.head
      case topLevel => topLevel
    }

    def analyzer(tree: Tree, previous: Tree, currentCtx: PREContext): PREContext = {
      tree match {
        case valDef: ValDef =>
          analyzer(valDef.rhs, valDef, currentCtx)

        case defDef: DefDef =>
          if (tree == previous) {
            val (state, traversal) = analyzer(defDef.rhs, defDef, currentCtx)
            val optimizedState = state.retainOptimizableExpressions
            val newContext = optimizedState -> traversal
            orderedContexts += (newContext -> tree)
            newContext
          } else currentCtx

        case block: Block =>
          (block.stats ::: List(block.expr)).foldLeft(currentCtx) {
            (context, subTree) => analyzer(subTree, block, context)
          }

        case tryCatch @ Try(expr, cases, finalizer) =>
          val newCtx = analyzer(expr, tryCatch, currentCtx)
          val (state, traversal) = newCtx
          val (_, diffedStats) = state.diff(currentCtx._1).get

          val caseSymbols: List[Symbol] = cases.map {
            case CaseDef(pat, guard, body) =>
              val first = getFirstInnerTree(body)
              registerEntrypointBasedOnTree(body, first)
          }
          val finalizerSymbol: Option[Symbol] = {
            if (finalizer == EmptyTree) None else {
              val first = getFirstInnerTree(finalizer)
              Some(registerEntrypointBasedOnTree(first, first))
            }
          }
          val updatedDiffStats = diffedStats.map { kv =>
            val (itree, (inits, stats)) = kv
            val newInits =
              if (finalizerSymbol.isEmpty) caseSymbols
              else finalizerSymbol.get :: caseSymbols
            val updatedInits = newInits ::: inits
            itree -> (updatedInits, stats)
          }

          val (counters, stats) = state.get
          State(counters -> (stats ++ updatedDiffStats)) -> traversal

        case branch @ If(cond, thenp, elsep) =>
          val state = analyzer(cond, branch, currentCtx)
          if (isUnitConstant(elsep)) state else {
            val analyzed = List(thenp, elsep).map(analyzer(_, branch, state))
            analyzed.reduceLeft { (accContext, newContext) =>
              // Traversal list is mutable, choose whichever
              accContext._1.intersect(newContext._1) -> newContext._2
            }
          }

        case tree: Tree =>
          IdempotentTrees.from(tree) match {
            case Some(idempotent) =>
              val allSubTrees = IdempotentTrees.allIdempotentTrees(idempotent)
              val (currentState, traversal) = currentCtx
              if (allSubTrees.nonEmpty) traversal += allSubTrees

              val initSymbol = registerEntrypointBasedOnTree(previous, tree)

              val newState = allSubTrees.foldLeft(currentState) { (state, st) =>
                val subTree = st.tree
                val (counters, stats) = state.get
                val currentCounter = counters.getOrElse(st, 0)
                val (inits, refs) = stats.getOrElse(st, EmptyIdempotentInfo)
                val newInits = if (inits.isEmpty) List(initSymbol) else inits
                val newRefs = subTree :: refs
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
    @inline def registerAssignation(assignation: Tree, at: Symbol) = {
      val otherTargets = assignations.getOrElse(at, List.empty[Tree])
      assignations += (at -> (assignation :: otherTargets))
    }

    def generateEntrypoint: ValDef =
      tpd.SyntheticValDef(ctx.freshName("entrypoint$$").toTermName, EmptyTree)

    def registerEntrypoint(at: Tree, pos: EntrypointPosition): Symbol = {
      val entrypoint = generateEntrypoint
      val entrypointSymbol = entrypoint.symbol
      entrypoints += entrypointSymbol
      needsEntrypoint += at -> (entrypoint -> pos)
      entrypointSymbol
    }

    def registerEntrypointBasedOnTree(previous: Tree, at: Tree): Symbol = {
      previous match {
        case valDef: ValOrDefDef => valDef.symbol
        case _: Block => registerEntrypoint(at, InsideBlock)
        case tree =>
          val symbol = tree.symbol
          if (symbol != NoSymbol) symbol
          else registerEntrypoint(at, InsideTreeAsTopLevel)
      }
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
      val flags = Flags.Synthetic | Flags.Mutable
      val rhs = cand.tree
      val (tpe, pos) = (rhs.tpe.widen, rhs.pos)
      val symbol = ctx.newSymbol(ctx.owner, name, flags, tpe, coord = pos)
      IdempotentTrees.markIdempotent(symbol)
      val valDef = tpd.ValDef(symbol, tpd.defaultValue(tpe))
      val ref = tpd.ref(symbol)
      val assign = Assign(ref, rhs)
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
              val alreadyAssigned = mutable.HashSet.empty[Symbol]
              val (lhs, rhs) = (assignation.lhs, assignation.rhs)
              inits.foreach { sym =>
                // Branches may introduce repeated assignations
                if (!alreadyAssigned.contains(sym)) {
                  alreadyAssigned += sym
                  // Apply recursive optimizations in the rhs
                  val updated = Assign(lhs, TreesUtils.replace(rhs, replacements))
                  registerAssignation(updated, sym)
                }
              }
              refs.foreach { ref =>
                // Remove inner trees replacement
                TreesUtils.delete(ref, replacements)
                replacements += ref -> reference
              }
              optimizedCache += itree
            }
          }
        }
      }

      orderedContexts.foreach(p => optimizeContext(p._1, p._2))

      {
        tree => needsEntrypoint.get(tree) match {
          case Some(entrypointInfo) =>
            needsEntrypoint -= tree
            val (entrypoint, pos) = entrypointInfo
            pos match {
              case InsideBlock =>
                tpd.Thicket(entrypoint, tree)
              case InsideTreeAsTopLevel =>
                tpd.Block(List(entrypoint), tree)
            }

          case None =>
            tree match {
              case Block(stats, expr) =>
                expr match {
                  case Thicket(trees) =>
                    // Expand tree if thicket is in expr position inside block
                    cpy.Block(tree)(stats = stats ::: trees.init,
                                    expr = trees.last)
                  case _ => tree
                }
              case _ => tree
            }
        }
      }
    }

    val transformer: Transformer = {
      case enclosing: ValOrDefDef =>
        // Introduce declarations or assignations of optimized ValDefs
        val enclosingSym = enclosing.symbol
        val newTrees = if (declarations.contains(enclosingSym)) {
          val result = declarations(enclosingSym).reverse
          declarations -= enclosingSym
          result
        } else if (assignations.contains(enclosingSym)) {
          val result = assignations(enclosingSym).reverse
          assignations -= enclosingSym
          result
        } else List.empty[ValDef]

        val removeEntrypoint = entrypoints.contains(enclosingSym)
        if (newTrees.nonEmpty) {
          if (true) println(i"Introducing ${newTrees.map(_.show)}")
          enclosing match {
            case defDef: DefDef =>
              val finalRhs = enclosing.rhs match {
                case blk @ Block(stats, expr) =>
                  cpy.Block(blk)(newTrees ::: stats, expr)
                case singleRhs =>
                  tpd.Block(newTrees, singleRhs)
              }
              val correctTypeRhs = finalRhs.tpe.widenIfUnstable
              cpy.DefDef(defDef)(rhs = finalRhs.withType(correctTypeRhs))
            case valDef: ValDef =>
              if (removeEntrypoint) tpd.Thicket(newTrees)
              else tpd.Thicket(newTrees ::: List(valDef))
          }
        } else if (removeEntrypoint) EmptyTree
        else enclosing

      case tree =>
        val resultingTree = replacements.get(tree) match {
          case Some(replacement) =>
            optimizedTimes = optimizedTimes + 1
            replacement
          case None => tree
        }
        if (debug && (resultingTree ne tree))
          println(s"Rewriting ${tree.show} to ${resultingTree.show}")
        resultingTree
    }

    (analyzer _, preOptimizer, transformer)
  }

  override def transformUnit(tree: tpd.Tree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    println(s"CSE removed $optimizedTimes expressions")
    tree
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
  def apply(tree: Tree)(implicit ctx: Context): IdempotentTree =
    new IdempotentTree(tree)

  def from(tree: Tree)(implicit ctx: Context): Option[IdempotentTree] =
    if (isIdempotent(tree)) Some(new IdempotentTree(tree)) else None

  def markIdempotent(sym: Symbol)(implicit ctx: Context) =
    ctx.idempotencyPhase.asInstanceOf[IdempotencyInference].markAsIdempotent(sym)

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
          if (!canBranch) collectValid(qual, canBranch = true)
          else IdempotentTrees(tree) :: collectValid(qual, canBranch = true)

        case TypeApply(fn, _) =>
          if (canBranch)
            IdempotentTrees(tree) :: collectValid(fn)
          else collectValid(fn)

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

}

object TreesUtils {

  import tpd.{Tree, cpy}
  import scala.collection.mutable

  /** Replace an **idempotent** subtree by a reference to another new tree. */
  def replace(tree: Tree, replacements: mutable.HashMap[Tree, Tree])
             (implicit ctx: Context) = {
    def loop(tree: Tree, topLevel: Boolean = false): Tree = {
      tree match {
        case _: Tree if replacements.contains(tree) =>
          // Exactly equal trees return the original reference
          if (topLevel) tree else replacements(tree)
        case Select(qual, name) => cpy.Select(tree)(loop(qual), name)
        case TypeApply(fn, targs) => cpy.TypeApply(tree)(loop(fn), targs)
        case Apply(fn, args) =>
          val replacedArgs = args.map(a => loop(a))
          cpy.Apply(tree)(loop(fn), replacedArgs)
        case t => t
      }
    }
    loop(tree, topLevel = true)
  }
  /** Delete a targeted already-known **idempotent** subtree. */
  def delete(tree: Tree, replacements: mutable.HashMap[Tree, Tree])
            (implicit ctx: Context) = {
    def loop(tree: Tree): Unit = {
      tree match {
        case _: Tree if replacements.contains(tree) => replacements -= tree
        case Select(qual, name) => loop(qual)
        case TypeApply(fn, targs) => loop(fn)
        case Apply(fn, args) =>
          args.foreach(loop)
          loop(fn)
        case t =>
      }
    }
    loop(tree)
  }

}

object State {

  import tpd.Tree
  type Counters = Map[IdempotentTree, Int]
  type IdempotentInfo = (List[Symbol], List[Tree])
  type IdempotentStats = Map[IdempotentTree, IdempotentInfo]

  val EmptyIdempotentInfo: IdempotentInfo =
    (List.empty[Symbol], List.empty[Tree])

  def apply(): State = State(
    Map[IdempotentTree, Int]() -> Map[IdempotentTree, IdempotentInfo]()
  )

}

case class State(get: (Counters, IdempotentStats)) extends AnyVal {

  def intersect(other: State): State = {
    val (cs, stats) = get
    val (cs2, stats2) = other.get

    val newCounters = cs.flatMap { pair =>
      val (key, value) = pair
      cs2.get(key).map(value2 => List(key -> (value + value2))).getOrElse(Nil)
    }

    val newInfo = stats.flatMap { pair =>
      val (key, value) = pair
      stats2.get(key).map { value2 =>
        val mixedInits = value._1 ++ value2._1
        val mixedRefs = value._2 ++ value2._2
        List(key -> (mixedInits -> mixedRefs))
      }.getOrElse(Nil)
    }

    State(newCounters -> newInfo)
  }

  def diff(other: State): State = {
    val (cs, stats) = get
    val (cs2, stats2) = other.get
    val commonCounters = cs.filter(kv => !cs2.contains(kv._1))
    val commonInfo = stats.filter(kv => !stats2.contains(kv._1))
    State(commonCounters -> commonInfo)
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

