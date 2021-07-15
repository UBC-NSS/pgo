package pgo.util

import pgo.model.{Definition, DefinitionOne, DerivedSourceLocation, PGoError, RefersTo, Rewritable, SourceLocatable, SourceLocation, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import Description._

import scala.annotation.tailrec
import scala.collection.mutable

object MPCalPassUtils {
  def forEachName(tlaModule: TLAModule, mpcalBlock: MPCalBlock)(fn: String => Unit): Unit = {
    tlaModule.moduleDefinitions(captureLocal = true).foreach { defn =>
      defn.identifier match {
        case Definition.ScopeIdentifierName(name) => fn(name.id)
        case Definition.ScopeIdentifierSymbol(symbol) => symbol.symbol.representations.foreach(fn)
      }
    }
    mpcalBlock.visit(Visitable.BottomUpFirstStrategy) {
      case ident: TLAIdentifier => fn(ident.id)
      case PCalLabeledStatements(label, _) => fn(label.name)
    }
  }

  def forEachBody(mpcalBlock: MPCalBlock)(fn: (List[PCalStatement], Map[String,DefinitionOne]) => Unit): Unit =
    rewriteEachBody(mpcalBlock) { (body, lexicalScope) =>
      fn(body, lexicalScope)
      body
    }

  def rewriteEachBody(mpcalBlock: MPCalBlock)(fn: (List[PCalStatement], Map[String,DefinitionOne]) => List[PCalStatement]): MPCalBlock =
    mpcalBlock.rewrite(Rewritable.TopDownFirstStrategy) {
      case blk @MPCalMappingMacro(name, readBody, writeBody, freeVars) =>
        val lexicalScope = freeVars.view.map(v => v.id.id -> v).toMap
        blk.withChildren(Iterator(
          name,
          fn(readBody, lexicalScope),
          fn(writeBody, lexicalScope),
          freeVars))
      case blk @PCalMacro(name, params, body, freeVars) =>
        blk.withChildren(Iterator(
          name, params,
          fn(body, (params.view.map(p => p.id.id -> p) ++ freeVars.view.map(v => v.id.id -> v)).toMap),
          freeVars))
      case blk @PCalProcedure(name, params, variables, body) =>
        blk.withChildren(Iterator(
          name, params, variables,
          fn(body, (params.view.map(p => p.name.id -> p) ++ variables.view.map(v => v.name.id -> v)).toMap)))
      case blk @MPCalProcedure(name, params, variables, body) =>
        blk.withChildren(Iterator(
          name, params, variables,
          fn(body, (params.view.map(p => p.name.id -> p) ++ variables.view.map(v => v.name.id -> v)).toMap)))
      case blk @PCalProcess(selfDecl, fairness, variables, body) =>
        blk.withChildren(Iterator(
          selfDecl, fairness, variables,
          fn(body, variables.view.map(v => v.name.id -> v).toMap.updated("self", selfDecl))))
      case blk @MPCalArchetype(name, selfDecl, params, variables, body) =>
        blk.withChildren(Iterator(
          name, selfDecl, params, variables,
          fn(body, (params.view.map(p => p.name.id -> p) ++ variables.view.map(v => v.name.id -> v)).toMap.updated("self", selfDecl))))
    }

  final case class MacroExpandError(override val errors: List[PGoError.Error]) extends PGoError

  object MacroExpandError {
    sealed abstract class Error(override val sourceLocation: SourceLocation, override val description: Description) extends PGoError.Error

    final case class ArgumentCountMismatchError(callNode: PCalMacroCall, definedAtNode: PCalMacro) extends Error(
      callNode.sourceLocation, d"expected ${definedAtNode.params.size} arguments, as defined at ${
        definedAtNode.sourceLocation.longDescription
      }\n but got ${callNode.arguments.size} instead")

    final case class UnboundFreeVariableError(freeVar: TLADefiningIdentifier, callNode: PCalMacroCall) extends Error(
      freeVar.sourceLocation, d"macro call at ${
        callNode.sourceLocation.longDescription
      }\n does not contextually bind free variable ${freeVar.id.id}")

    final case class MacroExpandAssignmentLhsError(lhs: PCalAssignmentLhsIdentifier, badExpr: TLAExpression) extends Error(
      lhs.sourceLocation, d"during macro expansion, an expression that is not a plain identifier, coming from ${
        badExpr.sourceLocation.longDescription
      }, would be expanded as a PlusCal assignment LHS")
  }

  def expandMacroCall(pcalMacroCall: PCalMacroCall, enclosingScope: Map[String,DefinitionOne]): List[PCalStatement] = {
    val m = pcalMacroCall.refersTo
    val errors = mutable.ListBuffer[PGoError.Error]()

    if(pcalMacroCall.arguments.size != m.params.size) {
      errors += MacroExpandError.ArgumentCountMismatchError(pcalMacroCall, m)
    }
    val paramsMap: Map[DefinitionOne,TLAExpression] = (m.params.iterator zip pcalMacroCall.arguments.iterator).toMap

    // make sure all free vars refer to something reasonable, and build a map of those references
    val referenceMapping: Map[DefinitionOne,DefinitionOne] = m.freeVars.iterator.flatMap { fv =>
      enclosingScope.get(fv.id.id) match {
        case Some(defn) => Iterator.single(fv -> defn)
        case None =>
          errors += MacroExpandError.UnboundFreeVariableError(fv, pcalMacroCall)
          Iterator.empty
      }
    }.toMap

    if(errors.nonEmpty) {
      throw MacroExpandError(errors.result())
    }

    // substitute out references to macro args; shallow-copy everything in order to add the macro expansion to
    // the source location.
    // side-effect: all nodes are effectively deep-copied, except macro args that should not refer to the macro's free vars,
    //  so we can mutate refersTo below without worrying about sharing
    val body: List[PCalStatement] = m.body.map(_.rewrite(Rewritable.BottomUpOnceStrategy) {
      case ref: PCalAssignmentLhsIdentifier if paramsMap.contains(ref.refersTo) =>
        paramsMap(ref.refersTo) match {
          case ident @TLAGeneralIdentifier(name, Nil) =>
            PCalAssignmentLhsIdentifier(name)
              .setSourceLocation(ident.sourceLocation)
              .setRefersTo(ident.refersTo)
          case badExpr =>
            throw MacroExpandError(List(MacroExpandError.MacroExpandAssignmentLhsError(ref, badExpr)))
        }
      case ref: RefersTo[TLADefiningIdentifier @unchecked] if paramsMap.contains(ref.refersTo) =>
        paramsMap(ref.refersTo): TLAExpression
      case ref: SourceLocatable =>
        ref.shallowCopy().setSourceLocation(
          DerivedSourceLocation(ref.sourceLocation, pcalMacroCall.sourceLocation, d"macro expansion"))
    })

    // remap all the references to free variables to point to what the free vars point to (relies on duplication, from above)
    body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
      case ref: RefersTo[DefinitionOne @unchecked] if referenceMapping.contains(ref.refersTo) =>
        ref.setRefersTo(referenceMapping(ref.refersTo))
    })
    body
  }

  def expandMacroCalls(stmts: List[PCalStatement], enclosingScope: Map[String,DefinitionOne]): List[PCalStatement] =
    stmts.flatMap {
      case stmt @PCalIf(condition, yes, no) =>
        List(stmt.withChildren(Iterator(
          condition,
          expandMacroCalls(yes, enclosingScope),
          expandMacroCalls(no, enclosingScope))))
      case stmt @PCalEither(cases) =>
        List(stmt.withChildren(Iterator(cases.map(expandMacroCalls(_, enclosingScope)))))
      case stmt @PCalLabeledStatements(label, statements) =>
        List(stmt.withChildren(Iterator(
          label,
          expandMacroCalls(statements, enclosingScope))))
      case macroCall: PCalMacroCall =>
        expandMacroCalls(expandMacroCall(macroCall, enclosingScope), enclosingScope)
      case stmt @PCalWhile(condition, body) =>
        List(stmt.withChildren(Iterator(
          condition,
          expandMacroCalls(body, enclosingScope))))
      case stmt @PCalWith(variables, body) =>
        List(stmt.withChildren(Iterator(
          variables,
          expandMacroCalls(
            body,
            variables.foldLeft(enclosingScope)((nestedScope, v) => nestedScope.updated(v.name.id, v))))))
      case stmt => List(stmt)
    }

  def gatherContainsLabels(mpcalBlock: MPCalBlock): IdSet[PCalStatement] = {
    var containsLabels = IdSet.empty[PCalStatement]
    def gatherContainsLabels(stmt: PCalStatement): Boolean = {
      // note: the seemingly over-engineered map+reduce ensures all sub-statements are reached,
      //   vs. a more concise but short-circuiting .exists(...)
      val result: Boolean = stmt match {
        case PCalEither(cases) => cases.view.flatMap(_.view.map(gatherContainsLabels)).foldLeft(false)(_ || _)
        case PCalIf(_, yes, no) =>
          yes.view.map(gatherContainsLabels).foldLeft(false)(_ || _) ||
            no.view.map(gatherContainsLabels).foldLeft(false)(_ || _)
        case PCalLabeledStatements(_, statements) =>
          statements.foreach(gatherContainsLabels)
          true
        case PCalWhile(_, body) => body.view.map(gatherContainsLabels).foldLeft(false)(_ || _)
        case PCalWith(_, body) => body.view.map(gatherContainsLabels).foldLeft(false)(_ || _)
        case _ => false
      }
      if(result) {
        containsLabels += stmt
      }
      result
    }

    mpcalBlock.visit(Visitable.TopDownFirstStrategy) {
      case stmt: PCalStatement => gatherContainsLabels(stmt)
    }

    containsLabels
  }

  object MappedRead {
    @tailrec
    private def unapplyImpl(expr: TLAExpression, mappingCount: Int): Option[(Int,TLAGeneralIdentifier)] =
      expr match {
        case TLAFunctionCall(fn, _) =>
          unapplyImpl(fn, mappingCount + 1)
        case ident: TLAGeneralIdentifier => Some((mappingCount, ident))
        case _ => None
      }

    def unapply(expr: TLAExpression): Option[(Int,TLAGeneralIdentifier)] =
      unapplyImpl(expr, mappingCount = 0)
  }
}
