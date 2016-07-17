package dotty.tools.dotc
package transform.linker
import core._
import Contexts.Context
import Flags._
import Symbols._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import StdNames._
import NameOps._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import util.Positions._
import java.util

import Names._
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.Phases.Phase
import dotty.tools.dotc.transform.{Splitter, TreeTransforms}
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo, TreeTransform}

import scala.collection.JavaConversions
import collection.mutable
import scala.collection.immutable.::

/** This phase applies rewritings provided by libraries. */
class IdempotencyInference extends MiniPhaseTransform with IdentityDenotTransformer {
  thisTransform =>
  def phaseName: String = "IdempotencyInference"
  import tpd._

  /** List of names of phases that should precede this phase */
  override def runsAfter: Set[Class[_ <: Phase]] = Set(classOf[Splitter])

  private val collectedCalls = mutable.Map[Symbol, mutable.Set[Symbol]]()
  private val inferredIdempotent = mutable.Set[Symbol]()

  // TODO: check overriding rules.

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo):tpd.Tree = {
    val calls = collection.mutable.Set[Symbol]()
    tree.rhs.foreachSubTree {
      case t: RefTree =>
        if (!t.symbol.isContainedIn(tree.symbol))
          calls += t.symbol
      case _ =>
    }

    collectedCalls.put(tree.symbol, calls)
    tree
  }


  override def transformUnit(tree: tpd.Tree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    var changed = true
    while (changed) {
      changed = false
      collectedCalls.foreach { case (defn, calls) =>
          if (!inferredIdempotent(defn)) {
            if (calls.forall(isIdempotentRef)) {
              changed = true
              inferredIdempotent += defn
              println(s"Inferred ${defn.showFullName} idempotent")
            }
          }
      }
    }

    tree
  }

  /** Expressions known to be initialized once are idempotent (lazy vals
   * and vals), as well as methods annotated with `Idempotent` */
  def isIdempotentRef(sym: Symbol)(implicit ctx: Context): Boolean = {
    if ((sym hasAnnotation defn.IdempotentAnnot) || inferredIdempotent(sym)) true // @Idempotent
    else if (sym is Lazy) true // lazy val and singleton objects
    else if (!(sym is Mutable) && !(sym is Method)) true // val
    else sym.isGetter && !(sym is Mutable)
  }

  def isIdempotent(tree: Tree)(implicit ctx: Context): Boolean = {

    tree match {
      case EmptyTree | This(_) | Super(_, _) | Literal(_) => true
      case Ident(_) => isIdempotentRef(tree.symbol)
      case Select(qual, _) => isIdempotent(qual) && isIdempotentRef(tree.symbol)
      case TypeApply(fn, _) => isIdempotent(fn)
      case Apply(fn, args) => isIdempotent(fn) && (args forall isIdempotent)
      case Typed(expr, _) => isIdempotent(expr)
      case _ => false
    }
  }
}

