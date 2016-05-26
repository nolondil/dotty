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
import dotty.tools.dotc.transform.Summaries.CallWithContext
import dotty.tools.dotc.transform.{BuildCallGraph, TreeTransforms}
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo, TreeTransform}
import scala.collection.JavaConversions
import collection.mutable
import scala.collection.immutable.::

/** This phase applies rewritings provided by libraries. */
class MinimizeClosures extends MiniPhaseTransform {
  thisTransform =>
  def phaseName: String = "minimizeClosures"

  override def transformClosure(tree: tpd.Closure)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    val analyzeClouresPhase = ctx.phaseOfClass(classOf[AnalyzeClosures]).asInstanceOf[AnalyzeClosures]
    val acessedFields = analyzeClouresPhase.accessedFileds

    acessedFields.get(tree.meth.symbol) match {
      case Some(fields) =>
        tree
      case None =>
        tree
    }
  }
}

