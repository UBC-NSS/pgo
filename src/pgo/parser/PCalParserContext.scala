package pgo.parser

import pgo.model.pcal._
import pgo.model.Definition
import pgo.model.tla.TLAIdentifier

final case class PCalParserContext()(implicit val ctx: TLAParserContext) {
  def withDefinition(defn: Definition): PCalParserContext =
    copy()(ctx.withDefinition(defn))

  def withProcessSelf(self: PCalVariableDeclarationBound): PCalParserContext =
    copy()(ctx.copy(
      currentScope = ctx.currentScope.updated(
        Definition.ScopeIdentifierName(TLAIdentifier("self").setSourceLocation(self.sourceLocation)),
        self)))

  def withLateBinding: PCalParserContext =
    copy()(ctx.withLateBinding)
}

object PCalParserContext {
  implicit def getTLAParserContext(implicit ctx: PCalParserContext): TLAParserContext = ctx.ctx
}
