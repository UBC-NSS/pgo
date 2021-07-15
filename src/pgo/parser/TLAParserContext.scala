package pgo.parser

import pgo.model.{Definition, DefinitionComposite, DefinitionOne}
import pgo.model.tla._

import scala.annotation.tailrec
import scala.collection.mutable

final case class TLAParserContext(minColumn: Int = -1,
                                  lateBindingStack: Int = 0,
                                  currentScope: Map[Definition.ScopeIdentifier,DefinitionOne] = Map.empty,
                                  functionSubstitutionPairAnchor: Option[TLAFunctionSubstitutionPairAnchor] = None) {
  def withMinColumn(minColumn: Int): TLAParserContext =
    copy(minColumn=minColumn)

  def withDefinition(defn: Definition): TLAParserContext =
    defn match {
      case defn: DefinitionOne =>
        copy(currentScope=currentScope.updated(defn.identifier, defn))
      case defn: DefinitionComposite => defn.singleDefinitions.foldLeft(this)(_.withDefinition(_))
    }

  def withFunctionSubstitutionPairAnchor(anchor: TLAFunctionSubstitutionPairAnchor): TLAParserContext =
    copy(functionSubstitutionPairAnchor = Some(anchor))

  def withLateBinding: TLAParserContext =
    copy(lateBindingStack = lateBindingStack + 1)

  def lookupModuleExtends(id: Definition.ScopeIdentifierName): TLAModuleRef =
    currentScope.get(id) match {
      case Some(defn: TLAModule) => TLAModuleRefModule(defn).setSourceLocation(id.sourceLocation)
      case Some(defn) => throw DoesNotExtendAModuleError(id, defn)
      case None => BuiltinModules.builtinModules.get(id) match {
        case Some(builtin) => TLAModuleRefBuiltin(builtin).setSourceLocation(id.sourceLocation)
        case None => throw ModuleNotFoundError(id)
      }
    }

  def instantiateModule(id: Definition.ScopeIdentifierName): TLAParserContext = {
    currentScope.get(id) match {
      case Some(defn: TLAModule) => ???
      case _ => ???
    }
  }

  def lookupDefinition(path: List[Definition.ScopeIdentifier]): Option[DefinitionOne] = {
    path match {
      case Nil => None
      case List(id) => currentScope.get(id)
      case id :: tl =>
        currentScope.get(id).flatMap(lookupDefinition(_, tl))
    }
  }

  @tailrec
  private def lookupDefinition(defn: DefinitionOne, path: List[Definition.ScopeIdentifier]): Option[DefinitionOne] =
    path match {
      case Nil => None
      case List(id) => defn.scope.get(id)
      case hd :: tl =>
        defn.scope.get(hd) match {
          case None => None
          case Some(defn) => lookupDefinition(defn, tl)
        }
    }
}
