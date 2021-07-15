package pgo.model

import scala.collection.View

sealed trait Definition {
  def singleDefinitions: View[DefinitionOne]
}

object Definition {
  sealed abstract class ScopeIdentifier {
    def sourceLocation: SourceLocation
  }
  object ScopeIdentifier {
    implicit val scopeIdentifierOrdered: Ordering[ScopeIdentifier] = Ordering.by[ScopeIdentifier,(Boolean,String)] {
      case ScopeIdentifierName(name) => (false, name.id)
      case ScopeIdentifierSymbol(symbol) => (true, symbol.symbol.representations.head)
    }
  }
  final case class ScopeIdentifierName(name: tla.TLAIdentifier) extends ScopeIdentifier {
    override def sourceLocation: SourceLocation = name.sourceLocation
  }
  final case class ScopeIdentifierSymbol(symbol: tla.TLASymbol) extends ScopeIdentifier {
    override def sourceLocation: SourceLocation = symbol.sourceLocation
  }
}

trait DefinitionOne extends Definition with RefersTo.HasReferences {
  override def singleDefinitions: View[DefinitionOne] = View(this)

  def arity: Int
  def identifier: Definition.ScopeIdentifier

  def isModuleInstance: Boolean = false
  def isLocal: Boolean = false
  def scope: Map[Definition.ScopeIdentifier, DefinitionOne] = Map.empty
}

trait DefinitionComposite extends Definition {
  def definitions: View[Definition]
  override def singleDefinitions: View[DefinitionOne] =
    definitions.flatMap(_.singleDefinitions)
}
