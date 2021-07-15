package pgo.model.mpcal

import pgo.model.{Definition, DefinitionOne, RefersTo, Rewritable, SourceLocatable}
import pgo.model.tla._
import pgo.model.pcal._

sealed abstract class MPCalNode extends Rewritable with SourceLocatable {
  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setSourceLocation(sourceLocation))
}

final case class MPCalRefExpr(name: TLAIdentifier, mappingCount: Int) extends MPCalNode with RefersTo[DefinitionOne]

final case class MPCalDollarValue() extends MPCalNode

final case class MPCalDollarVariable() extends MPCalNode

final case class MPCalYield(expr: TLAExpression) extends MPCalNode

final case class MPCalCall(target: TLAIdentifier, arguments: List[Either[MPCalRefExpr,TLAExpression]]) extends MPCalNode with RefersTo[MPCalProcedure]

sealed abstract class MPCalParam extends MPCalNode with DefinitionOne {
  def name: TLAIdentifier

  override def arity: Int = 0
  override def identifier: Definition.ScopeIdentifier = Definition.ScopeIdentifierName(name)
}
final case class MPCalRefParam(override val name: TLAIdentifier, mappingCount: Int) extends MPCalParam
final case class MPCalValParam(override val name: TLAIdentifier) extends MPCalParam

final case class MPCalBlock(name: TLAIdentifier, units: List[TLAUnit], macros: List[PCalMacro], mpcalProcedures: List[MPCalProcedure],
                            mappingMacros: List[MPCalMappingMacro], archetypes: List[MPCalArchetype],
                            variables: List[PCalVariableDeclaration], instances: List[MPCalInstance],
                            pcalProcedures: List[PCalProcedure],
                            processes: Either[List[PCalStatement],List[PCalProcess]]) extends MPCalNode

final case class MPCalProcedure(name: TLAIdentifier, params: List[MPCalParam], variables: List[PCalPVariableDeclaration],
                                body: List[PCalStatement]) extends MPCalNode with RefersTo.HasReferences

final case class MPCalMappingMacro(name: TLAIdentifier, readBody: List[PCalStatement], writeBody: List[PCalStatement],
                                   freeVars: List[TLADefiningIdentifier]) extends MPCalNode with RefersTo.HasReferences

final case class MPCalArchetype(name: TLAIdentifier, selfDecl: TLADefiningIdentifier, params: List[MPCalParam],
                                variables: List[PCalVariableDeclaration], body: List[PCalStatement]) extends MPCalNode with RefersTo.HasReferences

final case class MPCalInstance(selfDecl: PCalVariableDeclarationBound, fairness: PCalFairness,
                               archetypeName: TLAIdentifier, arguments: List[Either[MPCalRefExpr,TLAExpression]],
                               mappings: List[MPCalMapping]) extends MPCalNode with RefersTo[MPCalArchetype]

final case class MPCalMapping(target: MPCalMappingTarget, mappingMacroIdentifier: TLAIdentifier) extends MPCalNode with RefersTo[MPCalMappingMacro]

final case class MPCalMappingTarget(position: Int, mappingCount: Int) extends MPCalNode
