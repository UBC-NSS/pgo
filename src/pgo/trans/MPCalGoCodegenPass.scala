package pgo.trans

import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.{Description, IdMap, NameCleaner}
import Description._
import pgo.model.tla.BuiltinModules.TLABuiltinOperator
import pgo.util.MPCalPassUtils.MappedRead
import pgo.util.Unreachable.!!!

import java.util.Locale
import scala.annotation.tailrec
import scala.collection.{View, mutable}

object MPCalGoCodegenPass {
  private val TLAValue = "distsys.TLAValue"
  private val ArchetypeResourceHandle = "distsys.ArchetypeResourceHandle"
  val goKeywords: List[String] =
    """
      |break        default      func         interface    select
      |case         defer        go           map          struct
      |chan         else         goto         package      switch
      |const        fallthrough  if           range        type
      |continue     for          import       return       var
      |""".stripMargin.split(' ').view.filter(_.nonEmpty).toList

  sealed abstract class Binding {
    val bind: String
  }
  final case class IndependentCallableBinding(bind: String) extends Binding
  final case class DependentCallableBinding(bind: String) extends Binding
  final case class FixedValueBinding(bind: String) extends Binding
  final case class ResourceBinding(bind: String) extends Binding

  case class GoCodegenContext(nameCleaner: NameCleaner, bindings: IdMap[RefersTo.HasReferences,Binding] = IdMap.empty,
                              errOpt: Option[Description] = None,
                              ctxName: String, selfName: String, constantsName: String, constantsTypeName: String,
                              resourceMappingCounts: IdMap[RefersTo.HasReferences,Int] = IdMap.empty
                             ) {
    def err: Description = errOpt.get
    def cleanName[T](hint: String)(fn: String => T): T =
      fn(nameCleaner.cleanName(hint))
  }

  def toGoPublicName(id: String): String =
    id.capitalize

  // I think it's confusing that type of output is "Description". I know that it's probably because of borrowing the code
  // from 416 grader, but maybe it's better to rename it here.
  def translateMPCalCallable(callableName: String, selfDeclOpt: Option[TLADefiningIdentifier], params: List[MPCalParam], variables: List[PCalVariableDeclaration], body: List[PCalStatement])(implicit ctx: GoCodegenContext): Description = {
    assert(body.forall(_.isInstanceOf[PCalLabeledStatements]))
    val nameCleaner = ctx.nameCleaner

    val programCounterResourceName = nameCleaner.cleanName("programCounter")
    val err = nameCleaner.cleanName("err")

    val pcalEithers = locally {
      val acc = mutable.ListBuffer.empty[PCalEither]
      body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
        case either@PCalEither(_) => acc += either
      })
      acc.result()
    }
    val fairnessCounterNames = pcalEithers.view
      .map(either => either -> ctx.nameCleaner.cleanName("fairnessCounter"))
      .to(IdMap)

    val labelBinds = body.view.map {
      case PCalLabeledStatements(label, statements) =>
        label.name -> s"${ctx.nameCleaner.cleanName(label.name)}LabelTag"
    }.toMap

    // What does fn do here?
    def readExpr(expr: TLAExpression, hint: String = "resourceRead")(fn: Description=>Description)(implicit ctx: GoCodegenContext): Description = {
      val resourceReads = mutable.ListBuffer[(DefinitionOne,PCalVariableDeclarationEmpty,List[TLAExpression])]()
      lazy val readReplacer: PartialFunction[Rewritable,Rewritable] = {
        case expr@MappedRead(mappingCount, ident) if ctx.resourceMappingCounts.get(ident.refersTo).contains(mappingCount) =>
          @tailrec
          def findIndices(expr: TLAExpression, acc: mutable.ListBuffer[TLAExpression]): List[TLAExpression] =
            expr match {
              case _: TLAGeneralIdentifier => acc.result()
              case TLAFunctionCall(fn, params) =>
                if(params.size == 1) {
                  acc.prepend(params.head)
                } else {
                  acc.prepend(TLATuple(params))
                }
                findIndices(fn, acc)
            }

          val indices = findIndices(expr, mutable.ListBuffer.empty).map(_.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer))
          val cleanName = ctx.nameCleaner.cleanName(hint)
          val replacementDefn = PCalVariableDeclarationEmpty(TLAIdentifier(cleanName))
          val replacementAST = TLAGeneralIdentifier(TLAIdentifier(cleanName), Nil).setRefersTo(replacementDefn)
          resourceReads += ((ident.refersTo, replacementDefn, indices))
          replacementAST
        case ident@TLAGeneralIdentifier(_, prefix) =>
          assert(prefix.isEmpty)
          ctx.bindings(ident.refersTo) match {
            case ResourceBinding(_) =>
              val cleanName = ctx.nameCleaner.cleanName(hint)
              val replacementDefn = PCalVariableDeclarationEmpty(TLAIdentifier(cleanName))
              val replacementAST = TLAGeneralIdentifier(TLAIdentifier(cleanName), Nil).setRefersTo(replacementDefn)
              resourceReads += ((ident.refersTo, replacementDefn, Nil))
              replacementAST
            case _ => ident
          }
      }
      val exprWithReads = expr.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer)
      val origCtx = ctx
      locally {
        implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ resourceReads.view.map {
          case (_, replaceDefn, _) => replaceDefn -> FixedValueBinding(replaceDefn.name.id)
        })
        resourceReads.view.map {
          case (defn, replaceDefn, indices) =>
            d"\nvar ${replaceDefn.name.id} $TLAValue" +
              d"\n${replaceDefn.name.id}, ${ctx.err} = ${ctx.ctxName}.Read(${ctx.bindings(defn).bind}, []$TLAValue{${indices.view.map(translateExpr)}})" +
              d"\nif ${ctx.err} != nil {${
                d"\ncontinue".indented
              }\n}"
        }.flattenDescriptions +
          fn(translateExpr(exprWithReads))
      }
    }

    def readExprs(exprs: List[(TLAExpression,String)])(fn: List[Description]=>Description)(implicit ctx: GoCodegenContext): Description = {
      def impl(exprs: List[(TLAExpression,String)], acc: mutable.ListBuffer[Description]): Description =
        exprs match {
          case Nil => fn(acc.result())
          case (expr, hint) :: restExprs =>
            readExpr(expr, hint = hint) { exprRead =>
              acc.append(exprRead)
              impl(restExprs, acc)
            }
        }

      impl(exprs, mutable.ListBuffer[Description]())
    }

    def commit(body: =>Description)(implicit ctx: GoCodegenContext): Description =
      d"\n${ctx.err} = ${ctx.ctxName}.Commit()" +
        d"\nif ${ctx.err} != nil {${
          d"\ncontinue".indented
        }\n}" +
        body

    def goto(label: String)(implicit ctx: GoCodegenContext): Description =
      d"\n${ctx.err} = ${ctx.ctxName}.Write($programCounterResourceName, []$TLAValue{}, distsys.NewTLANumber(${labelBinds(label)}))" +
        d"\nif ${ctx.err} != nil {${
          d"\ncontinue".indented
        }\n}"

    def impl(stmts: List[PCalStatement], pfxDesc: Description = d"")(implicit ctx: GoCodegenContext): Description =
      stmts match {
        case Nil =>
          d"$pfxDesc\n// no statements"
        case PCalGoto(target) :: Nil =>
          pfxDesc + goto(target) + commit(d"")
        case PCalReturn() :: Nil =>
          pfxDesc + commit(d"\nreturn nil")
        case PCalExtensionStatement(call@MPCalCall(_, arguments)) :: restStmts =>
          ??? // generate a jump to a separate, synthetic block. this block will have its own PC, and control will
          // go through it to call the procedure. When the procedure returns, that block will take care of executing
          // the correct jump (not considered: tail calls).
          /*val exprArgs = arguments.collect { case Right(expr) => expr }
          val exprArgIndices = exprArgs.view.zipWithIndex.to(IdMap)
          pfxDesc + readExprs(exprArgs) { exprReads =>
            commit {
              val IndependentCallableBinding(nameToCall) = ctx.bindings(call.refersTo)
              d"\n${ctx.err} = $nameToCall(${ctx.constantsName}${
                arguments.map {
                  case Left(ref) => d", ${ctx.bindings(ref.refersTo).bind}"
                  case Right(expr) => d", ${exprReads(exprArgIndices(expr))}"
                }
              })" +
                d"\nif ${ctx.err} != nil {${
                  d"\nreturn err".indented
                }\n}" +
                (restStmts match {
                  case PCalGoto(target) :: Nil =>
                    d"\ngoto $target"
                  case PCalReturn() :: Nil =>
                    d"\nreturn nil"
                })
            }
          }*/
        case stmt :: restStmts =>
          val result = stmt match {
            case PCalAssert(condition) =>
              val conditionExpr = condition
              readExpr(condition, hint = "condition") { condition =>
                d"\nif !$condition.AsBool() {${
                  (d"""\n${ctx.err} = fmt.Errorf("%w: ${
                    escapeStringToGo(PCalRenderPass.describeExpr(conditionExpr).linesIterator.mkString("\n"))
                  }", distsys.AssertionFailed)""" +
                    d"\ncontinue").indented
                }\n}"
              }
            case PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) =>
              @tailrec
              def gatherLhsIndices(lhs: PCalAssignmentLhs, acc: mutable.ListBuffer[TLAExpression]): List[TLAExpression] =
                lhs match {
                  case PCalAssignmentLhsIdentifier(_) => acc.result()
                  case PCalAssignmentLhsProjection(lhs, projections) =>
                    if (projections.size == 1) {
                      acc.prepend(projections.head)
                    } else {
                      acc.prepend(TLATuple(projections))
                    }
                    gatherLhsIndices(lhs, acc)
                  case PCalAssignmentLhsExtension(_) => !!!
                }

              @tailrec
              def findLhsIdent(lhs: PCalAssignmentLhs): PCalAssignmentLhsIdentifier =
                lhs match {
                  case ident: PCalAssignmentLhsIdentifier => ident
                  case PCalAssignmentLhsProjection(lhs, _) => findLhsIdent(lhs)
                  case PCalAssignmentLhsExtension(_) => !!!
                }

              readExprs((rhs, "exprRead") :: gatherLhsIndices(lhs, mutable.ListBuffer.empty).map(_ -> "indexRead")) { exprReads =>
                d"\n${ctx.err} = ${ctx.ctxName}.Write(${ctx.bindings(findLhsIdent(lhs).refersTo).bind}, []$TLAValue{${exprReads.tail.separateBy(d", ")}}, ${exprReads.head})" +
                  d"\nif ${ctx.err} != nil {${
                    d"\ncontinue".indented
                  }\n}"
              }
            case PCalAwait(condition) =>
              readExpr(condition, hint = "condition") { condition =>
                d"\nif !$condition.AsBool() {${
                  (d"\n${ctx.err} = distsys.CriticalSectionAborted" +
                    d"\ncontinue").indented
                }\n}"
              }
            case PCalCall(_, _) => !!! // replaced by MPCalCall above
            case either@PCalEither(cases) =>
              ctx.cleanName(s"fairnessCounterCurrent") { fairnessCounterCurrent =>
                d"\n$fairnessCounterCurrent := ${fairnessCounterNames(either)}" +
                  d"\n${fairnessCounterNames(either)} = ${fairnessCounterNames(either)} + 1 % ${cases.size}" +
                  d"\nswitch $fairnessCounterCurrent {${
                    cases.view.zipWithIndex.map {
                      case (body, idx) =>
                        d"\ncase $idx:" +
                          impl(body).indented
                    }.flattenDescriptions +
                      d"\ndefault:" +
                      d"""\npanic("current branch of either matches no code paths!")""".indented
                  }\n}"
              }
            case PCalIf(condition, yes, no) =>
              readExpr(condition, hint = "condition") { condition =>
                d"\nif $condition.AsBool() {${
                  impl(yes).indented
                }\n} else {${
                  impl(no).indented
                }\n}"
              }
            case PCalLabeledStatements(_, _) => !!!
            case PCalMacroCall(_, _) => !!!
            case PCalPrint(value) =>
              readExpr(value, hint = "toPrint") { value =>
                d"\n$value.PCalPrint()"
              }
            case PCalSkip() =>
              d"\n// skip"
            case PCalWhile(_, _) => !!!
            case PCalWith(variables, body) =>
              readExprs(variables.map {
                case PCalVariableDeclarationValue(name, value) => (value, s"${name.id}Read")
                case PCalVariableDeclarationSet(name, set) => (set, s"${name.id}Read")
              }) { exprReads =>
                val oldCtx = ctx
                val cleanedNames = variables.map(decl => ctx.nameCleaner.cleanName(decl.name.id))
                ((variables.view zip exprReads) zip cleanedNames).map {
                  case ((PCalVariableDeclarationValue(_, _), read), name) =>
                    d"\nvar $name $TLAValue = $read"
                  case ((PCalVariableDeclarationSet(_, _), read), name) =>
                    d"\nvar $name $TLAValue = $read.SelectElement()"
                }.toList.flattenDescriptions + {
                  implicit val ctx: GoCodegenContext = oldCtx.copy(
                    bindings = oldCtx.bindings ++ (variables.view zip cleanedNames.view.map(FixedValueBinding)))
                  impl(body)
                }
              }
          }
          impl(restStmts, pfxDesc = pfxDesc + result)
      }

    val paramNames = params.view.map {
      case param@MPCalRefParam(name, _) => param -> nameCleaner.cleanName(name.id)
      case param@MPCalValParam(name) => param -> nameCleaner.cleanName(name.id)
    }.to(IdMap)
    val paramLocalNames = params.view.collect {
      case param@MPCalValParam(name) => param -> nameCleaner.cleanName(name.id)
    }.to(IdMap)
    val varNames = variables.view.map { decl =>
      decl -> nameCleaner.cleanName(decl.name.id)
    }.to(IdMap)

    val origCtx = ctx
    locally {
      implicit val ctx: GoCodegenContext = origCtx.copy(
        bindings = origCtx.bindings ++
          selfDeclOpt.map(selfDecl => selfDecl -> FixedValueBinding(origCtx.selfName)) ++
          paramNames.collect { case (param: MPCalRefParam) -> name => param -> ResourceBinding(name) } ++
          paramLocalNames.view.map { case param -> name => param -> ResourceBinding(name) } ++
          varNames.view.map { case v -> name => v -> ResourceBinding(name) },
        errOpt = Some(err.toDescription),
        resourceMappingCounts = params.view.collect {
          case param@MPCalRefParam(_, mappingCount) => param -> mappingCount
        }.to(IdMap),
      )

      def ensureLocalResource(value: Description): Description =
        d"distsys.EnsureLocalArchetypeResource(${ctx.ctxName}.ResourceEnsurerPositional(), $value)"

      d"\nfunc $callableName(${ctx.ctxName} *distsys.MPCalContext, ${ctx.selfName} $TLAValue, ${ctx.constantsName} ${ctx.constantsTypeName}${
        params.view.map {
          case param@MPCalRefParam(_, _) => d", ${paramNames(param)} $ArchetypeResourceHandle"
          case param@MPCalValParam(_) => d", ${paramNames(param)} $TLAValue"
        }.flattenDescriptions
      }) error {${
        (d"\nvar ${ctx.err} error" +
          d"\n// label tags" +
          d"\nconst (${
            (d"\n${labelBinds(body.head.asInstanceOf[PCalLabeledStatements].label.name)} = iota" +
              body.view.tail.map {
                case PCalLabeledStatements(label, _) =>
                  d"\n${labelBinds(label.name)}"
              }.flattenDescriptions).indented
          }\n)" +
          d"\n$programCounterResourceName := ${ensureLocalResource {
            val firstLabel = labelBinds(body.head.asInstanceOf[PCalLabeledStatements].label.name)
            d"distsys.NewTLANumber($firstLabel)"
          }}" +
          params.view.collect {
            case param: MPCalValParam =>
              d"\n${paramLocalNames(param)} := ${ensureLocalResource(paramNames(param).toDescription)}"
          }.flattenDescriptions +
          variables.view.map {
            case decl@PCalVariableDeclarationEmpty(_) =>
              d"\n${varNames(decl)} := ${ensureLocalResource(d"$TLAValue{}")}"
            case decl@PCalVariableDeclarationSet(_, set) =>
              d"\n${varNames(decl)} := ${ensureLocalResource(d"${translateExpr(set)}.SelectElement()")}"
            case decl@PCalVariableDeclarationValue(_, value) =>
              d"\n${varNames(decl)} := ${ensureLocalResource(translateExpr(value))}"
          }.flattenDescriptions +
          pcalEithers.map { either =>
            d"\nvar ${fairnessCounterNames(either)} int = 0"
          }.flattenDescriptions +
          d"\n" +
          d"\nfor {${
            (d"\nif $err != nil {${
              (d"\nif $err == distsys.CriticalSectionAborted {${
                (d"\nctx.Abort()" +
                  d"\n$err = nil").indented
              }\n} else {${
                d"\nreturn $err".indented
              }\n}").indented
            }\n}" +
              ctx.cleanName("labelTag") { labelTag =>
                d"\n$labelTag, ${ctx.err} := ${ctx.ctxName}.Read($programCounterResourceName, []$TLAValue{})" +
                  d"\nif ${ctx.err} != nil {${
                    d"\nreturn ${ctx.err}".indented
                  }\n}" +
                  d"\nswitch $labelTag.AsNumber() {${
                    body.map {
                      case PCalLabeledStatements(label, statements) =>
                        d"\ncase ${labelBinds(label.name)}:${
                          impl(statements).indented
                        }"
                    }
                  }\ndefault:${
                    d"""\nreturn fmt.Errorf("invalid program counter %v", $labelTag)""".indented
                  }\n}"
              }).indented
          }\n}").indented
      }\n}\n"
    }
  }

  def escapeStringToGo(str: String): String =
    str.flatMap {
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\t' => "\\t"
      case '\n' => "\\n"
      case '\f' => "\\f"
      case '\r' => "\\r"
      case ch => ch.toString
    }

  // What's the difference between readExpr and translateExpr?
  def translateExpr(expression: TLAExpression)(implicit ctx: GoCodegenContext): Description =
    expression match {
      case TLAString(value) =>
        d"""distsys.NewTLAString("${escapeStringToGo(value)}")"""
      case TLANumber(value, _) =>
        d"""distsys.NewTLANumber(${
          value match {
            case TLANumber.IntValue(value) => value.toString()
            case TLANumber.DecimalValue(value) => ??? //value.toString() // FIXME: should we be able to support this?
          }
        })"""
      case expr@MappedRead(mappingCount, ident) if ctx.resourceMappingCounts.get(ident.refersTo).contains(mappingCount) =>
        @tailrec
        def findIndices(expr: TLAExpression, acc: mutable.ListBuffer[TLAExpression]): List[TLAExpression] =
          expr match {
            case _: TLAGeneralIdentifier => acc.result()
            case TLAFunctionCall(fn, params) =>
              if(params.size == 1) {
                acc.prepend(params.head)
              } else {
                acc.prepend(TLATuple(params))
              }
              findIndices(fn, acc)
          }

        val indices = findIndices(expr, mutable.ListBuffer.empty).map(translateExpr).separateBy(d", ")
        d"${ctx.ctxName}.Read(${ctx.bindings(ident.refersTo).bind}, []$TLAValue{$indices})"
      case ident@TLAGeneralIdentifier(_, prefix) =>
        assert(prefix.isEmpty)
        ctx.bindings(ident.refersTo) match {
          case IndependentCallableBinding(bind) =>
            // only makes sense when:
            // - passing an operator to an operator
            // - reading an arity 0 built-in (which is basically like a constant)
            bind.toDescription
          case DependentCallableBinding(bind) =>
            val cleanArgs = View.fill(ident.refersTo.arity)(ctx.nameCleaner.cleanName("arg")).toList
            d"func(${cleanArgs.view.map(arg => d"$arg $TLAValue").separateBy(d", ")}) $TLAValue {${
              d"\nreturn $bind(${ctx.constantsName}${cleanArgs.view.map(arg => d", $arg").flattenDescriptions})"
            }\n}"
          case FixedValueBinding(bind) => bind.toDescription
          case ResourceBinding(_) => !!!
        }
      case TLADot(lhs, identifier) =>
        d"${translateExpr(lhs)}.ApplyFunction(${
          d"""distsys.NewTLAString("${identifier.id}")"""
        })"
      case call@TLAOperatorCall(_, prefix, arguments) =>
        assert(prefix.isEmpty)
        ctx.bindings(call.refersTo) match {
          case IndependentCallableBinding(bind) =>
            d"$bind(${arguments.map(translateExpr).separateBy(d", ")})"
          case DependentCallableBinding(bind) =>
            d"$bind(${ctx.constantsName}, ${arguments.map(translateExpr).separateBy(d", ")})"
        }
      case TLAIf(cond, tval, fval) =>
        d"func() {${
          (d"\nif ${translateExpr(cond)}.AsBool() {" +
            d"\nreturn ${translateExpr(tval)}".indented +
            d"\n} else {" +
            d"\nreturn ${translateExpr(fval)}".indented +
            d"\n}").indented
        }\n}()"
      case TLALet(defs, body) =>
        val origCtx = ctx
        d"func() $TLAValue {${
          val defnNames = defs.view.map {
            case defn@TLAOperatorDefinition(name, _, _, _) =>
              defn -> origCtx.nameCleaner.cleanName(name match {
                case Definition.ScopeIdentifierName(name) => name.id
                case Definition.ScopeIdentifierSymbol(symbol) => symbol.symbol.productPrefix
              })
          }.to(IdMap)
          implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ defs.view.map {
            case defn@TLAOperatorDefinition(_, Nil, _, _) => defn -> FixedValueBinding(defnNames(defn))
            case defn@TLAOperatorDefinition(_, _, _, _) => defn -> IndependentCallableBinding(defnNames(defn))
          })
          val origCtx2 = ctx
          (defs.view.map {
            case defn@TLAOperatorDefinition(_, Nil, body, _) =>
              d"\nvar ${defnNames(defn)} $TLAValue = ${translateExpr(body)}"
            case defn@TLAOperatorDefinition(_, args, body, _) =>
              val opDeclNames = args.view.map {
                case decl@TLAOpDecl(variant) =>
                  variant match {
                    case TLAOpDecl.NamedVariant(ident, _) => decl -> origCtx2.nameCleaner.cleanName(ident.id)
                    case TLAOpDecl.SymbolVariant(sym) => decl -> origCtx2.nameCleaner.cleanName(sym.symbol.productPrefix)
                  }
              }.to(IdMap)
              implicit val ctx: GoCodegenContext = origCtx2.copy(bindings = origCtx2.bindings ++ args.view.map {
                case decl@TLAOpDecl(variant) =>
                  variant match {
                    case TLAOpDecl.NamedVariant(_, 0) => decl -> FixedValueBinding(opDeclNames(decl))
                    case TLAOpDecl.NamedVariant(_, _) => decl -> IndependentCallableBinding(opDeclNames(decl))
                    case TLAOpDecl.SymbolVariant(_) => decl -> IndependentCallableBinding(opDeclNames(decl))
                  }
              })
              d"\n${defnNames(defn)} := func(${args.view.map { opDecl =>
                if(opDecl.arity == 0) {
                  d"${opDeclNames(opDecl)} $TLAValue"
                } else {
                  d"${opDeclNames(opDecl)} func(${View.fill(opDecl.arity)(TLAValue.toDescription).flattenDescriptions}) $TLAValue"
                }
              }.separateBy(d", ")}) $TLAValue {${
                d"\nreturn ${translateExpr(body)}".indented
              }\n}"
            case _ => !!!
          }.flattenDescriptions + d"\nreturn ${translateExpr(body)}").indented
        }\n}()"
      case TLACase(arms, other) =>
        d"func() $TLAValue {${
          d"switch {${
            arms.map {
              case TLACaseArm(cond, result) =>
                d"\ncase ${translateExpr(cond)}.AsBool():" +
                  d"\nreturn ${translateExpr(result)}".indented
            }.flattenDescriptions +
              d"\ndefault:" +
              other.map(other => d"\nreturn ${translateExpr(other)}")
                .getOrElse(d"""\npanic("no cases matched for TLA+ case expression!")""").indented
          }\n}"
        }\n}()"
      case TLAMaybeAction(_, _) => !!!
      case TLARequiredAction(_, _) => !!!
      case TLAFairness(_, _, _) => !!!
      case TLAFunction(args, body) =>
        ctx.cleanName("args") { argsName =>
          val origCtx = ctx
          d"distsys.NewTLAFunction([]$TLAValue{${args.view.map(_.set).map(translateExpr).separateBy(d", ")}}, func($argsName []$TLAValue) $TLAValue {${
            val argIds = args.view.flatMap {
              case TLAQuantifierBound(TLAQuantifierBound.IdsType, List(id), _) =>
                Some(id -> origCtx.nameCleaner.cleanName(id.id.id))
              case TLAQuantifierBound(TLAQuantifierBound.TupleType, elements, _) =>
                elements.view.map(id => id -> origCtx.nameCleaner.cleanName(id.id.id))
            }.to(IdMap)
            implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ argIds.map {
              case id -> name => id -> FixedValueBinding(name)
            })
            (args.view.zipWithIndex.flatMap {
              case (TLAQuantifierBound(TLAQuantifierBound.IdsType, List(id), _), idx) =>
                List(d"\nvar ${argIds(id)} $TLAValue = $argsName[$idx]")
              case (TLAQuantifierBound(TLAQuantifierBound.TupleType, elements, _), idx) =>
                elements.view.zipWithIndex.map {
                  case (element, elemIdx) =>
                    d"\nvar ${argIds(element)} $TLAValue = $argsName[$idx].FunctionApply(distsys.NewTLANumber($elemIdx))"
                }
            }.flattenDescriptions + d"\nreturn ${translateExpr(body)}").indented
          }\n})"
        }
      case TLAFunctionCall(function, params) =>
        d"${translateExpr(function)}.FunctionApply(${
          if(params.size == 1) {
            translateExpr(params.head)
          } else {
            d"distsys.NewTLATuple(${
              params.view.map(translateExpr).separateBy(d", ")
            })"
          }
        })"
      case TLAFunctionSet(from, to) =>
        d"distsys.NewTLAFunctionSet(${translateExpr(from)}, ${translateExpr(to)})"
      case TLAFunctionSubstitution(source, substitutions) => ???
      case at@TLAFunctionSubstitutionAt() =>
        val FixedValueBinding(name) = ctx.bindings(at.refersTo)
        name.toDescription
      case TLAQuantifiedExistential(bounds, body) => ???
      case TLAQuantifiedUniversal(bounds, body) => ???
      case TLAExistential(_, _) => !!!
      case TLAUniversal(_, _) => !!!
      case TLASetConstructor(contents) =>
        d"distsys.NewTLASet(${contents.view.map(translateExpr).separateBy(d", ")})"
      case TLASetRefinement(binding, when) => ???
      case TLASetComprehension(body, bounds) => ???
      case TLATuple(elements) =>
        d"distsys.NewTLATuple(${elements.view.map(translateExpr).separateBy(d", ")})"
      case TLARecordConstructor(fields) =>
        d"distsys.NewTLARecord([]distsys.TLARecordField{${
          fields.view.map {
            case TLARecordConstructorField(name, value) =>
              d"""\n{distsys.NewTLAString("${name.id}"), ${translateExpr(value)}},"""
          }.flattenDescriptions.indented
        }${if(fields.nonEmpty) d"\n" else d""}})"
      case TLARecordSet(fields) =>
        d"distsys.NewTLARecordSet([]distsys.TLARecordField{${
          fields.view.map {
            case TLARecordSetField(name, set) => d"""\n{distsys.NewTLAString("${name.id}"), ${translateExpr(set)}},"""
          }.flattenDescriptions.indented
        }${if(fields.nonEmpty) d"\n" else d""}})"
    }

  @throws[PGoError]
  def apply(tlaModule: TLAModule, mpcalBlock: MPCalBlock, packageName: Option[String]): Description = {
    val nameCleaner = new NameCleaner
    goKeywords.foreach(nameCleaner.addKnownName)
    nameCleaner.addKnownName("distsys")

    val Constants = nameCleaner.cleanName("Constants")

    val tlaExtDefns = (BuiltinModules.Intrinsics.members.view ++ tlaModule.exts.flatMap {
      // What's the difference between TLAModuleRefBuiltin and TLAModuleRefModule?
      case TLAModuleRefBuiltin(module) => module.members.view
      case TLAModuleRefModule(module) => ??? // TODO: actually implement modules
    }).toList

    val tlaExtDefnNames = tlaExtDefns.view.map {
      case defn@TLABuiltinOperator(_, identifier, _) =>
        identifier match {
          case Definition.ScopeIdentifierName(name) =>
            defn -> s"distsys.TLA_${name.id}"
          case Definition.ScopeIdentifierSymbol(symbol) =>
            defn -> s"distsys.TLA_${symbol.symbol.productPrefix}"
        }
    }.to(IdMap)

    val tlaUnits = (tlaModule.units.view.collect {
      case defn: TLAOperatorDefinition => defn
    } ++ mpcalBlock.units.view).toList

    val tlaUnitNames: IdMap[TLAUnit,String] = tlaUnits.view.map {
      case defn@TLAOperatorDefinition(name, _, _, _) =>
        name match {
          case Definition.ScopeIdentifierName(name) =>
            defn -> nameCleaner.cleanName(toGoPublicName(name.id))
          case Definition.ScopeIdentifierSymbol(symbol) =>
            defn -> nameCleaner.cleanName(toGoPublicName(symbol.symbol.productPrefix))
        }
    }.to(IdMap)

    val constantDecls = tlaModule.units.view.collect {
      case TLAConstantDeclaration(constants) => constants
    }.flatten.toList

    // depends on the "constants" parameter, has to be scoped _within_ any top-level definition
    val constantNames = constantDecls.view.map {
      case decl@TLAOpDecl(variant) =>
        variant match {
          case TLAOpDecl.NamedVariant(ident, _) => decl -> nameCleaner.cleanName(toGoPublicName(ident.id))
          case TLAOpDecl.SymbolVariant(sym) => decl -> nameCleaner.cleanName(toGoPublicName(sym.symbol.productPrefix))
        }
    }.to(IdMap)
    // I didn't understand why we need IdMap.

    val ctxName = nameCleaner.cleanName("ctx")
    val selfName = nameCleaner.cleanName("self")
    val constantsName = nameCleaner.cleanName("constants")

    implicit val ctx: GoCodegenContext = GoCodegenContext(
      nameCleaner = nameCleaner,
      ctxName = ctxName,
      selfName = selfName,
      constantsName = constantsName,
      constantsTypeName = Constants,
      bindings = (mpcalBlock.mpcalProcedures.view.map { proc =>
        proc -> IndependentCallableBinding(nameCleaner.cleanName(toGoPublicName(proc.name.id)))
      } ++ mpcalBlock.archetypes.view.map { arch =>
        arch -> IndependentCallableBinding(nameCleaner.cleanName(toGoPublicName(arch.name.id)))
      } ++ tlaExtDefnNames.map {
        case defn -> name => defn -> IndependentCallableBinding(name)
      } ++ constantDecls.view.map {
        case decl@TLAOpDecl(variant) =>
          variant match {
            case TLAOpDecl.NamedVariant(_, 0) => decl -> FixedValueBinding(s"$constantsName.${constantNames(decl)}")
            case TLAOpDecl.NamedVariant(_, _) => decl -> IndependentCallableBinding(s"$constantsName.${constantNames(decl)}")
            case TLAOpDecl.SymbolVariant(_) => decl -> IndependentCallableBinding(s"$constantsName.${constantNames(decl)}")
          }
      } ++ tlaUnits.view.map { defn =>
        defn.asInstanceOf[RefersTo.HasReferences] -> DependentCallableBinding(tlaUnitNames(defn))
      }).to(IdMap)
    )

    d"package ${packageName.getOrElse(mpcalBlock.name.id.toLowerCase(Locale.ROOT)): String}\n" +
      d"\nimport (${
        (d"""\n"github.com/UBC-NSS/pgo/distsys"""" +
          d"""\n"fmt\n"""").indented
      })\n" +
      d"\ntype $Constants struct {${
        constantDecls.map {
          case decl@TLAOpDecl(variant) =>
            variant match {
              case TLAOpDecl.NamedVariant(_, 0) =>
                d"\n${constantNames(decl)} $TLAValue"
              case TLAOpDecl.NamedVariant(_, arity) =>
                d"\n${constantNames(decl)} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")} $TLAValue"
              case TLAOpDecl.SymbolVariant(sym) =>
                val arity = if (sym.symbol.isPrefix) 1 else if (sym.symbol.isPostfix) 1 else { assert(sym.symbol.isInfix); 2 }
                d"\n${constantNames(decl)} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")} $TLAValue"
            }
        }.flattenDescriptions.indented
      }\n}\n" +
      tlaUnits.view.map {
        case defn@TLAOperatorDefinition(name, args, body, _) =>
          val origCtx = ctx
          val argNames = args.view.map {
            case decl@TLAOpDecl(variant) =>
              variant match {
                case TLAOpDecl.NamedVariant(ident, 0) =>
                  decl -> FixedValueBinding(nameCleaner.cleanName(ident.id))
                case TLAOpDecl.NamedVariant(ident, _) =>
                  decl -> IndependentCallableBinding(nameCleaner.cleanName(ident.id))
                case TLAOpDecl.SymbolVariant(sym) =>
                  decl -> IndependentCallableBinding(nameCleaner.cleanName(sym.symbol.productPrefix))
              }
          }.to(IdMap)
          d"\nfunc ${tlaUnitNames(defn)}($constantsName $Constants${args.view.map {
            case decl@TLAOpDecl(variant) =>
              variant match {
                case TLAOpDecl.NamedVariant(_, 0) => d", ${argNames(decl).bind} $TLAValue"
                case TLAOpDecl.NamedVariant(_, arity) => d", ${argNames(decl).bind} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")}) $TLAValue"
                case TLAOpDecl.SymbolVariant(sym) =>
                  val arity = if(sym.symbol.isInfix) 2 else 1
                  d", ${argNames(decl).bind} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")}) $TLAValue"
              }
          }.flattenDescriptions}) $TLAValue {${
            implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ argNames)
            d"\nreturn ${translateExpr(body)}".indented
          }\n}\n"
      }.flattenDescriptions + // TODO: procedures
      mpcalBlock.archetypes.view.map { arch =>
        translateMPCalCallable(ctx.bindings(arch).bind,
          selfDeclOpt = Some(arch.selfDecl), params = arch.params, variables = arch.variables, body = arch.body)
      }.flattenDescriptions
  }
}
