package pgo.parser

import pgo.model.Definition
import pgo.model.mpcal.{MPCalArchetype, MPCalMappingMacro}
import pgo.model.tla.TLAIdentifier

final case class MPCalParserContext(mappingMacros: Map[TLAIdentifier,MPCalMappingMacro] = Map.empty,
                                    archetypes: Map[TLAIdentifier,MPCalArchetype] = Map.empty)(implicit val ctx: PCalParserContext) {
  def withDefinition(defn: Definition): MPCalParserContext =
    copy()(ctx.withDefinition(defn))

  def withArchetype(archetype: MPCalArchetype): MPCalParserContext =
    copy(archetypes = archetypes.updated(archetype.name, archetype))

  def withMappingMacro(mappingMacro: MPCalMappingMacro): MPCalParserContext =
    copy(mappingMacros = mappingMacros.updated(mappingMacro.name, mappingMacro))

  def withLateBinding: MPCalParserContext =
    copy()(ctx.withLateBinding)
}

object MPCalParserContext {
  implicit def getPCalParserContext(implicit ctx: MPCalParserContext): PCalParserContext = ctx.ctx
}
