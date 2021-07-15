package pgo.trans

import pgo.model.tla._
import pgo.model.pcal._
import pgo.model.mpcal._
import pgo.util.Description
import Description._
import pgo.model.Definition

import scala.collection.View

object PCalRenderPass {
  def describeQuantifierBound(qb: TLAQuantifierBound): Description =
    qb.tpe match {
      case TLAQuantifierBound.IdsType =>
        d"${qb.ids.map(_.id.id.toDescription).separateBy(d", ")} \\in ${describeExpr(qb.set)}"
      case TLAQuantifierBound.TupleType =>
        d"<<${qb.ids.map(_.id.id.toDescription).separateBy(d", ")}>> \\in ${describeExpr(qb.set)}"
    }

  def describePrefix(prefix: List[TLAGeneralIdentifierPart]): Description =
    prefix.view.map {
      case TLAGeneralIdentifierPart(id, parameters) =>
        d"${id.id}(${
          parameters.view.map(describeExpr).separateBy(d", ")
        })!"
    }.flattenDescriptions

  def describeExpr(expr: TLAExpression): Description =
    expr match {
      case TLAExtensionExpression(MPCalDollarVariable()) => d"$$variable"
      case TLAExtensionExpression(MPCalDollarValue()) => d"$$value"
      case TLAString(value) =>
        d""""${
          value.flatMap {
            case '"' => "\\\""
            case '\\' => "\\\\"
            case '\t' => "\\t"
            case '\n' => "\\n"
            case '\f' => "\\f"
            case '\r' => "\\r"
            case ')' => "\\)" // these last two are extras, to allow writing (* and *) in MPCal comments
            case '*' => "\\*"
            case ch => ch.toString
          }
        }""""
      case TLANumber(value, _ /* force decimal representation, should be correct in most cases */) =>
        value match {
          case TLANumber.IntValue(value) =>
            value.toString().toDescription
          case TLANumber.DecimalValue(value) =>
            value.toString().toDescription
        }
      case TLAGeneralIdentifier(name, prefix) =>
        d"${describePrefix(prefix)}${name.id}"
      case TLADot(lhs, identifier) =>
        d"(${describeExpr(lhs)}).${identifier.id}"
      case TLAOperatorCall(name, prefix, arguments) =>
        name match {
          case Definition.ScopeIdentifierName(name) =>
            d"${describePrefix(prefix)}${name.id}(${
              arguments.view.map(describeExpr).separateBy(d", ")
            })"
          case Definition.ScopeIdentifierSymbol(symbol) =>
            if(symbol.symbol.isPrefix) {
              val List(operand) = arguments
              d"${describePrefix(prefix)}${symbol.symbol.stringReprUsage} (${describeExpr(operand)})"
            } else if(symbol.symbol.isPostfix) {
              val List(operand) = arguments
              d"(${describeExpr(operand)}) ${describePrefix(prefix)}${symbol.symbol.stringReprUsage}"
            } else {
              assert(symbol.symbol.isInfix)
              val List(lhs, rhs) = arguments
              d"(${describeExpr(lhs)}) ${describePrefix(prefix)}${symbol.symbol.stringReprUsage} (${describeExpr(rhs)})"
            }
        }
      case TLAIf(cond, tval, fval) =>
        d"IF ${describeExpr(cond)} THEN ${describeExpr(tval)} ELSE ${describeExpr(fval)}"
      case TLALet(defs, body) =>
        d"LET ${
          defs.view.map(describeUnit(_).ensureLineBreakAfter)
            .flattenDescriptions.indented
        } IN ${describeExpr(body)}"
      case TLACase(TLACaseArm(cond1, result1) :: armsRest, other) =>
        d"CASE ${describeExpr(cond1)} -> ${describeExpr(result1)}${
          armsRest.view.map {
            case TLACaseArm(cond, result) =>
              d"\n[] ${describeExpr(cond)} -> ${describeExpr(result)}"
          }.flattenDescriptions.indented
        }${
          other.map { other =>
            d"\n[] OTHER -> ${describeExpr(other)}".indented
          }.getOrElse(d"")
        }"
      case TLAMaybeAction(body, vars) =>
        d"[${describeExpr(body)}]_${describeExpr(vars)}"
      case TLARequiredAction(body, vars) =>
        d"<<${describeExpr(body)}>>_${describeExpr(vars)}"
      case TLAFairness(kind, vars, expression) =>
        kind match {
          case TLAFairness.StrongFairness =>
            d"WF_${describeExpr(expression)}(${describeExpr(vars)})"
          case TLAFairness.WeakFairness =>
            d"SF_${describeExpr(expression)}(${describeExpr(vars)})"
        }
      case TLAFunction(args, body) =>
        d"[${args.view.map(describeQuantifierBound).separateBy(d", ")} |-> ${describeExpr(body)}]"
      case TLAFunctionCall(function, params) =>
        d"(${describeExpr(function)})[${
          params.view.map(describeExpr).separateBy(d", ")
        }]"
      case TLAFunctionSet(from, to) =>
        d"[${describeExpr(from)} -> ${describeExpr(to)}]"
      case TLAFunctionSubstitution(source, substitutions) =>
        d"[${describeExpr(source)} EXCEPT ${
          substitutions.view.map {
            case TLAFunctionSubstitutionPair(anchor, keys, value) =>
              d"!${
                keys.view.map {
                  case TLAFunctionSubstitutionKey(indices) =>
                    d"[${indices.view.map(describeExpr).separateBy(d", ")}]"
                }.flattenDescriptions
              } = ${describeExpr(value)}"
          }.separateBy(d", ")
        }]"
      case TLAFunctionSubstitutionAt() => d"@"
      case TLAQuantifiedExistential(bounds, body) =>
        d"\\E ${bounds.view.map(describeQuantifierBound).separateBy(d", ")} : ${describeExpr(body)}"
      case TLAQuantifiedUniversal(bounds, body) =>
        d"\\A ${bounds.view.map(describeQuantifierBound).separateBy(d", ")} : ${describeExpr(body)}"
      case TLAExistential(ids, body) =>
        d"\\EE ${ids.view.map(_.id.id.toDescription).separateBy(d", ")} : ${describeExpr(body)}"
      case TLAUniversal(ids, body) =>
        d"\\AA ${ids.view.map(_.id.id.toDescription).separateBy(d", ")} : ${describeExpr(body)}"
      case TLASetConstructor(contents) =>
        d"{${contents.view.map(describeExpr).separateBy(d", ")}}"
      case TLASetRefinement(binding, when) =>
        d"{${describeQuantifierBound(binding)} : ${describeExpr(when)}}"
      case TLASetComprehension(body, bounds) =>
        d"{${describeExpr(body)} : ${bounds.view.map(describeQuantifierBound).separateBy(d", ")}}"
      case TLATuple(elements) =>
        d"<<${elements.view.map(describeExpr).separateBy(d", ")}>>"
      case TLARecordConstructor(fields) =>
        if(fields.isEmpty) {
          d"[ ]" // or else this empty case will be parsed as the temporal "always" prefix operator
        } else {
          d"[${
            fields.view.map {
              case TLARecordConstructorField(name, value) =>
                d"${name.id} |-> ${describeExpr(value)}"
            }.separateBy(d", ")
          }]"
        }
      case TLARecordSet(fields) =>
        if(fields.isEmpty) {
          d"[ ]" // same as above, avoids confusion with temporal "always" operator []
        } else {
          d"[${
            fields.view.map {
              case TLARecordSetField(name, set) =>
                d"${name.id} : ${describeExpr(set)}"
            }.separateBy(d", ")
          }]"
        }
    }

  def describeOpDecl(opDecl: TLAOpDecl): Description =
    opDecl.variant match {
      case TLAOpDecl.NamedVariant(ident, 0) =>
        ident.id.toDescription
      case TLAOpDecl.NamedVariant(ident, arity) =>
        d"${ident.id}(${View.fill(arity)(d"_").separateBy(d", ")})"
      case TLAOpDecl.SymbolVariant(sym) =>
        if(sym.symbol.isPrefix) {
          d"${sym.symbol.stringReprDefn} _"
        } else if(sym.symbol.isPostfix) {
          d"_ ${sym.symbol.stringReprDefn}"
        } else {
          assert(sym.symbol.isInfix)
          d"_ ${sym.symbol.stringReprDefn} _"
        }
    }

  def describeUnit(unit: TLAUnit, ignoreLocal: Boolean = false): Description =
    unit match {
      case TLAAssumption(assumption) =>
        d"ASSUME ${describeExpr(assumption)}"
      case TLAConstantDeclaration(constants) =>
        d"CONSTANTS ${constants.view.map(describeOpDecl).separateBy(d", ")}"
      case TLAInstance(moduleName, remappings, isLocal) =>
        d"${if(isLocal && !ignoreLocal) d"LOCAL " else d""}INSTANCE ${moduleName.id}${
          if(remappings.nonEmpty) {
            d" WITH ${
              remappings.view.map {
                case TLAInstanceRemapping(from, to) =>
                  from match {
                    case Definition.ScopeIdentifierName(name) =>
                      d"${name.id} <- ${describeExpr(to)}"
                    case Definition.ScopeIdentifierSymbol(symbol) =>
                      d"${symbol.symbol.stringReprDefn} <- ${describeExpr(to)}"
                  }
              }.separateBy(d", ")
            }"
          } else d""
        }"
      case TLAModule(name, exts, units) =>
        d"---- MODULE ${name.id} ----${
          if(exts.nonEmpty) {
            d"\nEXTENDS ${exts.view.map(_.identifier.name.id.toDescription).separateBy(d", ")}"
          } else d""
        }${
          units.view.map(describeUnit(_).ensureLineBreakBefore).flattenDescriptions
        }\n===="
      case TLAModuleDefinition(name, args, instance, isLocal) =>
        d"${if(isLocal && !ignoreLocal) d"LOCAL " else d""}${name.id}(${
          args.view.map(describeOpDecl).separateBy(d", ")
        }) == ${describeUnit(instance)}"
      case TLAOperatorDefinition(name, args, body, isLocal) =>
        d"${if(isLocal && !ignoreLocal) d"LOCAL " else d""}${
          name match {
            case Definition.ScopeIdentifierName(name) if args.isEmpty =>
              d"${name.id} == ${describeExpr(body)}"
            case Definition.ScopeIdentifierName(name) =>
              d"${name.id}(${args.view.map(describeOpDecl).separateBy(d", ")}) == ${describeExpr(body)}"
            case Definition.ScopeIdentifierSymbol(symbol) =>
              if(symbol.symbol.isPrefix) {
                val List(TLAOpDecl(TLAOpDecl.NamedVariant(id, 0))) = args
                d"${symbol.symbol.stringReprDefn} ${id.id} == ${describeExpr(body)}"
              } else if(symbol.symbol.isPostfix) {
                val List(TLAOpDecl(TLAOpDecl.NamedVariant(id, 0))) = args
                d"${id.id} ${symbol.symbol.stringReprDefn} == ${describeExpr(body)}"
              } else {
                assert(symbol.symbol.isInfix)
                val List(TLAOpDecl(TLAOpDecl.NamedVariant(idLhs, 0)), TLAOpDecl(TLAOpDecl.NamedVariant(idRhs, 0))) = args
                d"${idLhs.id} ${symbol.symbol.stringReprDefn} ${idRhs.id} == ${describeExpr(body)}"
              }
          }
        }"
      case TLATheorem(theorem) =>
        d"THEOREM ${describeExpr(theorem)}"
      case TLAVariableDeclaration(variables) =>
        d"VARIABLES ${variables.view.map(_.id.id.toDescription).separateBy(d", ")}"
    }

  def describeStatement(stmt: PCalStatement): Description =
    stmt match {
      case PCalExtensionStatement(MPCalCall(target, arguments)) =>
        d"call ${target.id}(${
          arguments.view.map {
            case Left(MPCalRefExpr(name, mappingCount)) =>
              d"ref ${name.id}${View.fill(mappingCount)(d"[_]").flattenDescriptions}"
            case Right(expr) => describeExpr(expr)
          }.separateBy(d", ")
        })"
      case PCalAssert(condition) =>
        d"assert ${describeExpr(condition)}"
      case PCalAssignment(pairs) =>
        def describeLhs(lhs: PCalAssignmentLhs): Description =
          lhs match {
            case PCalAssignmentLhsIdentifier(identifier) =>
              identifier.id.toDescription
            case PCalAssignmentLhsProjection(lhs, projections) =>
              d"${describeLhs(lhs)}[${projections.view.map(describeExpr).separateBy(d", ")}]"
            case PCalAssignmentLhsExtension(MPCalDollarVariable()) =>
              d"$$variable"
            case PCalAssignmentLhsExtension(contents) =>
              d"?? ${contents.toString} ??"
          }

        pairs.view.map {
          case PCalAssignmentPair(lhs, rhs) =>
            d"${describeLhs(lhs)} := ${describeExpr(rhs)}"
        }.separateBy(d" || ")
      case PCalAwait(condition) =>
        d"await ${describeExpr(condition)}"
      case PCalCall(target, arguments) =>
        d"call ${target.id}(${arguments.view.map(describeExpr).separateBy(d", ")})"
      case PCalEither(cases) =>
        d"either ${
          cases.view.map { block =>
            d"{\n${describeStatements(block).indented}\n}"
          }.separateBy(d" or ")
        }"
      case PCalGoto(target) =>
        d"goto $target"
      case PCalIf(condition, yes, no) =>
        d"if(${describeExpr(condition)}) {\n${
          describeStatements(yes).indented
        }\n}${
          if(no.nonEmpty) {
            d" else {\n${describeStatements(no).indented}\n}"
          } else d""
        }"
      case PCalLabeledStatements(label, statements) =>
        d"${label.name}${
          label.modifier match {
            case PCalLabel.PlusModifier => d"-"
            case PCalLabel.MinusModifier => d"+"
            case PCalLabel.NoModifier => d""
          }
        }:\n${describeStatements(statements, tailSemicolon = false).indented}"
      case PCalMacroCall(target, arguments) =>
        d"${target.id}(${arguments.view.map(describeExpr).separateBy(d", ")})"
      case PCalPrint(value) =>
        d"print ${describeExpr(value)}"
      case PCalReturn() => d"return"
      case PCalSkip() => d"skip"
      case PCalWhile(condition, body) =>
        d"while(${describeExpr(condition)}) {\n${
          describeStatements(body).indented
        }\n}"
      case PCalWith(variables, body) =>
        d"with (${variables.view.map(describeVarDecl).separateBy(d", ")}) {\n${
          describeStatements(body).indented
        }\n}"
    }

  def describeStatements(stmts: List[PCalStatement], tailSemicolon: Boolean = true): Description =
    if(tailSemicolon) {
      stmts.view.map(stmt => d"${describeStatement(stmt)};".ensureLineBreakBefore)
        .flattenDescriptions
    } else {
      stmts.view.map(stmt => d"${describeStatement(stmt)}".ensureLineBreakBefore)
        .separateBy(d";")
    }

  def describeVarDecl(varDecl: PCalVariableDeclaration): Description =
    varDecl match {
      case PCalVariableDeclarationEmpty(name) => name.id.toDescription
      case PCalVariableDeclarationValue(name, value) => d"${name.id} = ${describeExpr(value)}"
      case PCalVariableDeclarationSet(name, set) => d"${name.id} \\in ${describeExpr(set)}"
    }

  def apply(pcalAlgorithm: PCalAlgorithm): Description = {
    val PCalAlgorithm(fairness, name, variables, units, macros, procedures, processes) = pcalAlgorithm

    val header = fairness match {
      case PCalFairness.Unfair => d"--algorithm"
      case PCalFairness.WeakFair => d"--fair algorithm"
      case PCalFairness.StrongFair => d"--fair+ algorithm" // TODO: is this correct? we can't parse this
    }

    d"$header ${name.id} {${
      if(variables.nonEmpty) {
        d"\nvariables${
          variables.view.map { decl =>
            d" ${describeVarDecl(decl)};"
          }.flattenDescriptions
        }".indented
      } else d""
    }${
      if(units.nonEmpty) {
        d"\ndefine{${
          units.view.map { unit =>
            d"\n${describeUnit(unit)}".indented
          }.flattenDescriptions
        }\n}".indented
      } else d""
    }${
      macros.view.map {
        case PCalMacro(name, params, body, _) =>
          d"\n\nmacro ${name.id}(${
            params.view.map(_.id.id.toDescription).separateBy(d", ")
          }) {${
            describeStatements(body).indented
          }\n}"
      }.flattenDescriptions
    }${
      procedures.view.map {
        case PCalProcedure(name, params, variables, body) =>
          d"\n\nprocedure ${name.id}(${
            params.view.map {
              case PCalPVariableDeclaration(name, value) =>
                d"${name.id}${value.map(v => d" = ${describeExpr(v)}").getOrElse(d"")}"
            }.separateBy(d", ")
          })${
            if(variables.nonEmpty) {
              d"variables${
                variables.view.map {
                  case PCalPVariableDeclaration(name, value) =>
                    d" ${name.id}${value.map(v => d" = ${describeExpr(v)};").getOrElse(d"")}"
                }.flattenDescriptions
              }"
            } else d""
          }\n{${
            describeStatements(body).indented
          }\n}"
      }.flattenDescriptions
    }${
      processes match {
        case Left(statements) =>
          d"\n{${
            describeStatements(statements).indented
          }\n}"
        case Right(processes) =>
          processes.view.map {
            case PCalProcess(selfDecl, fairness, variables, body) =>
              d"\n\n${
                fairness match {
                  case PCalFairness.Unfair => d""
                  case PCalFairness.WeakFair => d"fair "
                  case PCalFairness.StrongFair => d"fair+ "
                }
              }process (${describeVarDecl(selfDecl)})${
                if(variables.nonEmpty) {
                  d"\nvariables${
                    variables.view.map { decl =>
                      d" ${describeVarDecl(decl)};"
                    }.flattenDescriptions
                  }".indented
                } else d""
              }\n{\n${
                describeStatements(body).indented
              }\n}"
          }.flattenDescriptions.indented
      }
    }\n}"
  }
}
