package pgo.parser

import pgo.model.{Definition, DefinitionOne, PGoError, SourceLocation}
import pgo.model.tla.{TLAGeneralIdentifierPart, TLAIdentifier}
import pgo.model.mpcal.MPCalArchetype
import pgo.util.Description
import Description._

sealed abstract class ParsingError(override val sourceLocation: SourceLocation, override val description: Description) extends PGoError with PGoError.Error {
  override val errors: List[PGoError.Error] = List(this)
}

final case class DefinitionLookupError(pfx: List[TLAGeneralIdentifierPart], id: Definition.ScopeIdentifier) extends ParsingError(
  id.sourceLocation,d"identifier ${pfx.mkString("!")}${if(pfx.nonEmpty){"!"} else {""}}${
    id match {
      case Definition.ScopeIdentifierName(name) => name.id
      case Definition.ScopeIdentifierSymbol(symbol) => symbol.symbol.stringReprUsage
    }} does not refer to a known definition")

final case class DoesNotExtendAModuleError(id: Definition.ScopeIdentifierName, badDefn: DefinitionOne) extends ParsingError(
  id.sourceLocation,d"${id.name.id} does not refer to a module. actually refers to ${badDefn.toString}")

final case class ModuleNotFoundError(id: Definition.ScopeIdentifierName) extends ParsingError(
  id.sourceLocation,d"module ${id.name.id} not found")

final case class MacroLookupError(target: TLAIdentifier) extends ParsingError(
  target.sourceLocation, d"could not find definition for macro `${target.id}`")

final case class ProcedureLookupError(target: TLAIdentifier) extends ParsingError(
  target.sourceLocation, d"could not find definition for procedure ${target.id}")

final case class ArchetypeLookupError(target: TLAIdentifier) extends ParsingError(
  target.sourceLocation, d"could not find referenced archetype ${target.id}")

final case class MappingLookupError(target: TLAIdentifier) extends ParsingError(
  target.sourceLocation,d"could not find referenced instance argument ${target.id}")

final case class MappingIndexOutOfBounds(loc: SourceLocation, idx: Int, maxIdx: Int) extends ParsingError(
  loc, d"index-referenced instance argument out of bounds: $idx, with largest valid index $maxIdx")

final case class MappingMacroLookupError(target: TLAIdentifier) extends ParsingError(
  target.sourceLocation, d"could not find referenced mapping macro ${target.id}")

final case class ArityMismatchError(loc: SourceLocation, defn: DefinitionOne, actualArity: Int) extends ParsingError(
  loc, d" arity mismatch: expected ${defn.arity}, found $actualArity")

final case class ArchetypeArityMismatchError(loc: SourceLocation, archetype: MPCalArchetype, actualArity: Int) extends ParsingError(
  loc, d"archetype arity mismatch: expected ${archetype.params.size}, found $actualArity")

final case class KindMismatchError(loc: SourceLocation, explanation: Description) extends ParsingError(
  loc, d"kind mismatch: $explanation")

final case class FunctionSubstitutionAtError(loc: SourceLocation) extends ParsingError(
  loc, d"function substitution anchor (the @ expression) found outside EXCEPT expression")

final case class ParseFailureError(err: String, loc: SourceLocation) extends ParsingError(
  loc, d"parsing failed: $err")
