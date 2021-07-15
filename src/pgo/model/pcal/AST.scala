package pgo.model.pcal

import pgo.model.{Definition, DefinitionOne, RefersTo, Rewritable, SourceLocatable, Visitable}
import pgo.model.tla._


sealed abstract class PCalNode extends Rewritable with SourceLocatable {
  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setSourceLocation(sourceLocation))
}

sealed abstract class PCalFairness
object PCalFairness {
  case object Unfair extends PCalFairness
  case object WeakFair extends PCalFairness
  case object StrongFair extends PCalFairness
}

final case class PCalDefaultInitValue() extends PCalNode

final case class PCalAlgorithm(fairness: PCalFairness, name: TLAIdentifier, variables: List[PCalVariableDeclaration],
                               units: List[TLAUnit], macros: List[PCalMacro], procedures: List[PCalProcedure],
                               processes: Either[List[PCalStatement],List[PCalProcess]]) extends PCalNode

final case class PCalPVariableDeclaration(name: TLAIdentifier, value: Option[TLAExpression]) extends PCalNode with DefinitionOne {
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = Definition.ScopeIdentifierName(name)
}

sealed abstract class PCalVariableDeclaration extends PCalNode with DefinitionOne {
  def name: TLAIdentifier
  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = Definition.ScopeIdentifierName(name)
}

final case class PCalVariableDeclarationEmpty(name: TLAIdentifier) extends PCalVariableDeclaration

sealed abstract class PCalVariableDeclarationBound extends PCalVariableDeclaration
final case class PCalVariableDeclarationValue(name: TLAIdentifier, value: TLAExpression) extends PCalVariableDeclarationBound
final case class PCalVariableDeclarationSet(name: TLAIdentifier, set: TLAExpression) extends PCalVariableDeclarationBound

final case class PCalMacro(name: TLAIdentifier, params: List[TLADefiningIdentifier], body: List[PCalStatement],
                           freeVars: List[TLADefiningIdentifier]) extends PCalNode with RefersTo.HasReferences

final case class PCalProcedure(name: TLAIdentifier, params: List[PCalPVariableDeclaration],
                               variables: List[PCalPVariableDeclaration], body: List[PCalStatement]) extends PCalNode with RefersTo.HasReferences

final case class PCalProcess(selfDecl: PCalVariableDeclarationBound, fairness: PCalFairness,
                             variables: List[PCalVariableDeclaration], body: List[PCalStatement]) extends PCalNode

sealed abstract class PCalStatement extends PCalNode

final case class PCalExtensionStatement(contents: Any) extends PCalStatement

final case class PCalAssert(condition: TLAExpression) extends PCalStatement

final case class PCalAssignment(pairs: List[PCalAssignmentPair]) extends PCalStatement

final case class PCalAssignmentPair(lhs: PCalAssignmentLhs, rhs: TLAExpression) extends PCalNode

sealed abstract class PCalAssignmentLhs extends PCalNode
final case class PCalAssignmentLhsIdentifier(identifier: TLAIdentifier) extends PCalAssignmentLhs with RefersTo[DefinitionOne]
final case class PCalAssignmentLhsProjection(lhs: PCalAssignmentLhs, projections: List[TLAExpression]) extends PCalAssignmentLhs
final case class PCalAssignmentLhsExtension(contents: Any) extends PCalAssignmentLhs

final case class PCalAwait(condition: TLAExpression) extends PCalStatement

final case class PCalCall(target: TLAIdentifier, arguments: List[TLAExpression]) extends PCalStatement with RefersTo[PCalProcedure]

final case class PCalEither(cases: List[List[PCalStatement]]) extends PCalStatement {
  require(cases.nonEmpty, s"either must have at least one case")
}

// target is a string, because it would be much too hard to integrate gotos (which can reference any local label) into RefersTo
final case class PCalGoto(target: String) extends PCalStatement

final case class PCalIf(condition: TLAExpression, yes: List[PCalStatement], no: List[PCalStatement]) extends PCalStatement

final case class PCalLabel(name: String, modifier: PCalLabel.Modifier) extends PCalNode
object PCalLabel {
  sealed abstract class Modifier
  case object PlusModifier extends Modifier
  case object MinusModifier extends Modifier
  case object NoModifier extends Modifier
}

final case class PCalLabeledStatements(label: PCalLabel, statements: List[PCalStatement]) extends PCalStatement

final case class PCalMacroCall(target: TLAIdentifier, arguments: List[TLAExpression]) extends PCalStatement with RefersTo[PCalMacro]

final case class PCalPrint(value: TLAExpression) extends PCalStatement

final case class PCalReturn() extends PCalStatement

final case class PCalSkip() extends PCalStatement

final case class PCalWhile(condition: TLAExpression, body: List[PCalStatement]) extends PCalStatement

final case class PCalWith(variables: List[PCalVariableDeclarationBound], body: List[PCalStatement]) extends PCalStatement
