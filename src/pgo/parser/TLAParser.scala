package pgo.parser

import pgo.model.{Definition, DefinitionOne, SourceLocatable, SourceLocation, SourceLocationWithUnderlying, Visitable}
import pgo.model.tla._
import pgo.util.Description
import pgo.model.Definition.ScopeIdentifierName
import pgo.util.Description.DescriptionHelper

import scala.collection.mutable
import scala.util.parsing.combinator.RegexParsers


trait TLAParser extends RegexParsers {
  override def skipWhitespace: Boolean = false
  val anything: Parser[Unit] = accept("anything", { case _ => () })

  def checkMinColumn(implicit ctx : TLAParserContext) : Parser[Unit] = { in =>
    val lcIn = in.asInstanceOf[LineColumnAwareCharReader]
    if (lcIn.column < ctx.minColumn) {
      Failure(s"insufficient indentation ${lcIn.column}, expected at least ${ctx.minColumn}", in)
    } else {
      Success((), in)
    }
  }

  def querySourceLocation[T](p: Parser[T]): Parser[(SourceLocation,T)] = {
    final case class GetSourceLocation[T](value: T) extends SourceLocatable
    withSourceLocation(p.map(GetSourceLocation(_))).map {
      case getter @GetSourceLocation(value) =>
        (getter.sourceLocation, value)
    }
  }

  def withSourceLocation[T <: SourceLocatable](p: =>Parser[T]): Parser[T] = {
    lazy val pp: Parser[T] = p // ensure p is evaluated at-most-once
    (in: Input) => {
      val lcIn = in.asInstanceOf[LineColumnAwareCharReader]
      pp(in).flatMapWithNext[T]((t: T) => (nextIn: Input) => {
        val lcNextIn = nextIn.asInstanceOf[LineColumnAwareCharReader]
        Success(
          t.setSourceLocation(SourceLocation(lcIn.underlyingText, startOffset = lcIn.offset, endOffset = lcNextIn.offset,
            startLine = lcIn.line, endLine = lcNextIn.line, startColumn = lcIn.column, endColumn = lcNextIn.column)),
          nextIn)
      })
    }
  }

  implicit class SymbolParser(sym: TLASymbol.Symbol) extends Parser[TLASymbol] {
    private lazy val underlying = withSourceLocation {
      sym.representations.foldRight(failure(s"expected $sym"): Parser[String])(_ | _) ^^ (_ => TLASymbol(sym))
    }
    override def apply(in: Input): ParseResult[TLASymbol] = underlying(in)
  }

  val tlaLineComment : Parser[Unit] =
    ("\\*" ~ rep(acceptIf(_ != '\n')(c => s"'$c' was a new line"))) ^^^ ()

  val tlaMultilineComment : Parser[Unit] = {
    val body = rep1(not("(*" | "*)" | "\\*") ~> anything)
    ("(*" ~ rep {
      tlaMultilineComment | tlaLineComment | body
    } ~ "*)") ^^^ ()
  }

  val tlaWhitespace : Parser[Unit] = rep(regex(raw"\s+".r) | tlaMultilineComment | tlaLineComment).map(_ => ())

  def wsChk(implicit ctx: TLAParserContext): Parser[Unit] = tlaWhitespace ~ checkMinColumn ^^^ ()

  val tlaIdentifier : Parser[String] = {
    val identRegex = raw"(?!WF_)(?!SF_)[a-z0-9_A-Z]*[a-zA-Z][a-z0-9_A-Z]*".r

    regex(identRegex) ^? ({
      case candidate if !TLAMeta.reservedWords.contains(candidate) &&
        !candidate.startsWith("WF_") &&
        !candidate.startsWith("SF_") => candidate
    }, candidate => s"expected identifier: $candidate is reserved word, or starts with WF_ or SF_")
  }

  val tlaString : Parser[String] =
    elem('\"') ~> (rep[Char] {
      (elem('\\') ~>! {
        elem('\"') | elem('\\') | ("t" ^^^ '\t') | ("n" ^^^ '\n') | ("f" ^^^ '\f') | ("r" ^^^ '\r') |
          elem(')') | elem('*')
      }.withFailureMessage("expected valid string escape: one of \\\", \\t, \\n, \\f, \\r, \\*, or \\)")) |
        acceptMatch("string contents", { case c if c != '\"' => c })
    } ^^ { parts => parts.mkString("") }) <~ elem('\"')

  val tlaIdentifierExpr: Parser[TLAIdentifier] =
    withSourceLocation(tlaIdentifier ^^ TLAIdentifier)

  val tlaStringExpr : Parser[TLAString] =
    withSourceLocation(tlaString ^^ TLAString)

  val tlaNumberExpr: Parser[TLANumber] =
    withSourceLocation {
      {
        regex(raw"\d+".r) ^^ { str => (TLANumber.IntValue(BigInt(str)), TLANumber.DecimalSyntax) } |
          regex(raw"\d*\.\d+".r) ^^ { str => (TLANumber.DecimalValue(BigDecimal(str)), TLANumber.DecimalSyntax) } |
          regex(raw"\\[bB][01]+".r) ^^ { str => (TLANumber.IntValue(BigInt(str.stripPrefix("b").stripPrefix("B"), 2)), TLANumber.BinarySyntax) } |
          regex(raw"\\[oO][0-7]+".r) ^^ { str => (TLANumber.IntValue(BigInt(str.stripPrefix("o").stripPrefix("O"), 8)), TLANumber.OctalSyntax) } |
          regex(raw"\\[hH][0-9a-fA-F]+".r) ^^ { str => (TLANumber.IntValue(BigInt(str.stripPrefix("h").stripPrefix("H"), 16)), TLANumber.HexadecimalSyntax) }
      } ^^ {
        case (value, syntax) => TLANumber(value, syntax)
      }
    }

  def tlaCommaSep[T](p: =>Parser[T])(implicit ctx: TLAParserContext): Parser[List[T]] =
    repsep(p, wsChk ~> "," <~ wsChk)

  def tlaComma1Sep[T](p: =>Parser[T])(implicit ctx: TLAParserContext): Parser[List[T]] =
    rep1sep(p, wsChk ~> "," <~ wsChk)

  def tlaIdentifierOrTupleQuantifierBound(implicit ctx: TLAParserContext): Parser[TLAQuantifierBound] = {
    val idOrTuple: Parser[Either[List[TLAIdentifier],TLAIdentifier]] =
      "<<" ~> wsChk ~> tlaCommaSep(tlaIdentifierExpr) <~ wsChk <~ ">>" ^^ (Left(_)) | tlaIdentifierExpr ^^ (Right(_))
    withSourceLocation {
      idOrTuple ~ (wsChk ~> "\\in" ~> wsChk ~> tlaExpression) ^^ {
        case Left(ids) ~ set => TLAQuantifierBound(TLAQuantifierBound.TupleType, ids.map(_.toDefiningIdentifier), set)
        case Right(id) ~ set => TLAQuantifierBound(TLAQuantifierBound.IdsType, List(id.toDefiningIdentifier), set)
      }
    }
  }

  def tlaQuantifierBound(implicit ctx: TLAParserContext): Parser[TLAQuantifierBound] =
    withSourceLocation {
      (("<<" ~> wsChk ~> tlaCommaSep(tlaIdentifierExpr) <~ wsChk <~ ">>" <~ wsChk <~ "\\in") ~ (wsChk ~> tlaExpression)) ^^ {
        case ids ~ set => TLAQuantifierBound(TLAQuantifierBound.TupleType, ids.map(_.toDefiningIdentifier), set)
      } |
        ((tlaComma1Sep(tlaIdentifierExpr) <~ wsChk <~ "\\in") ~ (wsChk ~> tlaExpression)) ^^ {
          case ids ~ set => TLAQuantifierBound(TLAQuantifierBound.IdsType, ids.map(_.toDefiningIdentifier), set)
        }
    }

  def tlaInstancePrefix(implicit ctx: TLAParserContext): Parser[List[TLAGeneralIdentifierPart]] = {
    final case class PrefixPart(part: TLAGeneralIdentifierPart, defn: DefinitionOne) extends SourceLocatable {
      override def setSourceLocation(sourceLocation: SourceLocation): this.type = {
        part.setSourceLocation(sourceLocation)
        super.setSourceLocation(sourceLocation)
      }
    }

    def impl(pfx: List[TLAGeneralIdentifierPart]): Parser[List[TLAGeneralIdentifierPart]] = {
      withSourceLocation {
        tlaIdentifierExpr.flatMap { id =>
          ctx.lookupDefinition(pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition.ScopeIdentifierName(id)) match {
            case None =>
              failure(s"lookup failed for identifier ${pfx.map(_.id.id).mkString("!")}!${id.id}")
            case Some(defn) =>
              if (defn.arity == 0) {
                // the extra negation is to avoid matching parts of an EXCEPT expression, where an id might be followed by !
                wsChk ~> "!" ~> not(wsChk ~> "[" ~> tlaWhitespace) ^^^ PrefixPart(TLAGeneralIdentifierPart(id, Nil), defn)
              } else {
                wsChk ~> "(" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ ")" <~ wsChk <~ "!" <~ not(wsChk ~> "[" ~> tlaWhitespace) ^^ { args =>
                  PrefixPart(TLAGeneralIdentifierPart(id, args), defn)
                }
              }
          }
        }
      }.flatMap {
        case PrefixPart(idPart, defn) =>
          if(!defn.isModuleInstance) {
            throw KindMismatchError(idPart.sourceLocation, d"expected module instance, found operator or variable")
            //failure(s"kind mismatch: expected module instance, found operator or variable `${defn.identifier.asInstanceOf[ScopeIdentifierName].name.id}`")
          }
          if(idPart.parameters.length != defn.arity) {
            throw ArityMismatchError(idPart.sourceLocation, defn, idPart.parameters.length)
            //failure(s"arity mismatch: definition has arity ${defn.arity}, mismatched with ${idPart.parameters.length}")
          }
          val path = pfx :+ idPart
          opt(wsChk ~> impl(path)) ^^ (_.getOrElse(path))
      }
    }

    (impl(Nil) | success(Nil)).withFailureMessage("expected instance prefix")
  }

  def tlaTupleExpr(implicit ctx: TLAParserContext): Parser[TLATuple] =
    withSourceLocation {
      "<<" ~> wsChk ~> tlaCommaSep(tlaExpression) <~ wsChk <~ ">>" ^^ TLATuple
    }

  def tlaRequiredActionExpr(implicit ctx: TLAParserContext): Parser[TLARequiredAction] =
    withSourceLocation {
      ("<<" ~> wsChk ~> tlaExpression <~ wsChk <~ ">>_") ~! (wsChk ~> tlaExpression) ^^ {
        case body ~ vars => TLARequiredAction(body, vars)
      }
    }

  def tlaOperatorCallOrGeneralIdentifier(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    withSourceLocation {
      (tlaInstancePrefix ~ (not(wsChk ~> "[") ~> wsChk ~> tlaIdentifierExpr)).flatMap {
        case pfx ~ id =>
          val name = Definition.ScopeIdentifierName(id)
          ctx.lookupDefinition(pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ name) match {
            case None =>
              if(ctx.lateBindingStack > 0 && pfx.isEmpty) {
                // if the context allows late bindings (i.e names bound to the right)
                // then assume arity == 0 and expect whoever incremented lateBindingStack to gather and handle
                // the unbound identifier
                success(TLAGeneralIdentifier(id, Nil))
              } else {
                // don't fail hard; it's possible that the prefix is empty and the identifier is an ambiguous
                // prefix of some other piece of syntax; perhaps an OpDecl
                failure(s"lookup failed for identifier ${pfx.map(_.id.id).mkString("!")}!${id.id}")
              }
            case Some(defn) =>
              if( defn.arity > 0 ) {
                (wsChk ~> "(" ~> wsChk ~> repsep(tlaExpression, wsChk ~> "," <~ wsChk) <~ wsChk <~ ")") ^^ { args =>
                  if(defn.arity != args.size) {
                    throw ArityMismatchError(id.sourceLocation, defn, args.size)
                  }
                  TLAOperatorCall(name, pfx, args).setRefersTo(defn)
                }
              } else {
                if(defn.arity != 0) {
                  throw ArityMismatchError(id.sourceLocation, defn, 0)
                }
                success(TLAGeneralIdentifier(id, pfx).setRefersTo(defn))
              }
          }
      }
    }

  def tlaConjunctOrDisjunct(which: String)(implicit ctx: TLAParserContext): Parser[TLAExpression] = {
    val origCtx = ctx
    guard(querySourceLocation(which)).flatMap {
      case (loc: SourceLocationWithUnderlying @unchecked, _) =>
        val lCtx = origCtx.withMinColumn(loc.startColumn)
        val rCtx = origCtx.withMinColumn(loc.startColumn + 1)
        implicit val ctx: TLAParserContext = rCtx
        rep1({
          implicit val ctx: TLAParserContext = lCtx
          wsChk ~> querySourceLocation(which)
        } ~ (wsChk ~> tlaExpression)) ^^ { parts =>
          val (_, resultExpr) = parts.tail.foldLeft((parts.head._1._1, parts.head._2)) { (acc, part) =>
            val (locationAcc, lhs) = acc
            val (symLoc, _) ~ rhs = part
            val combinedLoc = locationAcc ++ rhs.sourceLocation
            val sym = TLASymbol(TLASymbol.forString(which)).setSourceLocation(symLoc)
            val binop = TLAOperatorCall(Definition.ScopeIdentifierSymbol(sym), Nil, List(lhs, rhs))
              .setSourceLocation(combinedLoc)
            // should always succeed, /\ and \/ are built-in
            binop.setRefersTo(ctx.lookupDefinition(List(Definition.ScopeIdentifierSymbol(sym))).get)
            (combinedLoc, binop)
          }
          resultExpr
        }
    }
  }

  def tlaConjunctExpr(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaConjunctOrDisjunct("/\\")

  def tlaDisjunctExpr(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaConjunctOrDisjunct("\\/")

  def tlaIfExpr(implicit ctx: TLAParserContext): Parser[TLAIf] =
    withSourceLocation {
      ("IF" ~>! wsChk ~> tlaExpression) ~ (wsChk ~> "THEN" ~>! wsChk ~> tlaExpression) ~
        (wsChk ~> "ELSE" ~>! wsChk ~> tlaExpression) ^^ {
        case cond ~ yes ~ no => TLAIf(cond, yes, no)
      }
    }

  def tlaCaseExpr(implicit ctx: TLAParserContext): Parser[TLACase] =
    withSourceLocation {
      locally {
        withSourceLocation {
          "CASE" ~>! wsChk ~> tlaExpression ~ (wsChk ~> "->" ~> wsChk ~> tlaExpression) ^^ {
            case cond1 ~ res1 => TLACaseArm(cond1, res1)
          }
        } ~
          (wsChk ~> repsep(withSourceLocation("[]" ~> wsChk ~> tlaExpression ~ (wsChk ~> "->" ~> wsChk ~> tlaExpression) ^^ {
            case cond ~ res => TLACaseArm(cond, res)
          }), wsChk)) ~
          opt(wsChk ~> "[]" ~> wsChk ~> "OTHER" ~>! wsChk ~> "->" ~> wsChk ~> tlaExpression)
      } ^^ {
        case arm1 ~ arms ~ other =>
          TLACase(arm1 :: arms, other)
      }
    }

  def tlaFunctionExpr(implicit ctx: TLAParserContext): Parser[TLAFunction] = {
    val origCtx = ctx
    withSourceLocation {
      ("[" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "|->" <~! wsChk).flatMap { bounds =>
        implicit val ctx: TLAParserContext = bounds.foldLeft(origCtx)(_.withDefinition(_))
        (tlaExpression <~ wsChk <~ "]") ^^ ((bounds, _))
      } ^^ {
        case (qbs, expr) => TLAFunction(qbs, expr)
      }
    }
  }

  def tlaRecordSetExpr(implicit ctx: TLAParserContext): Parser[TLARecordSet] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaComma1Sep {
        withSourceLocation {
          tlaIdentifierExpr ~ (wsChk ~> ":" ~>! wsChk ~> tlaExpression) ^^ {
            case name ~ set => TLARecordSetField(name, set)
          }
        }
      } <~ wsChk <~ "]" ^^ TLARecordSet
    }

  def tlaRecordConstructorExpr(implicit ctx: TLAParserContext): Parser[TLARecordConstructor] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaComma1Sep {
        withSourceLocation {
          tlaIdentifierExpr ~ (wsChk ~> "|->" ~>! wsChk ~> tlaExpression) ^^ {
            case label ~ value => TLARecordConstructorField(label, value)
          }
        }
      } <~ wsChk <~ "]" ^^ TLARecordConstructor
    }

  def tlaFunctionSetExpr(implicit ctx: TLAParserContext): Parser[TLAFunctionSet] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "->" ~>! wsChk ~> tlaExpression <~ wsChk <~ "]") ^^ {
        case from ~ to => TLAFunctionSet(from, to)
      }
    }

  def tlaMaybeActionExpr(implicit ctx: TLAParserContext): Parser[TLAMaybeAction] =
    withSourceLocation {
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "]_" ~>! wsChk ~> tlaExpression) ^^ {
        case body ~ vars => TLAMaybeAction(body, vars)
      }
    }

  def tlaFunctionSubstitutionAtExpr(implicit ctx: TLAParserContext): Parser[TLAFunctionSubstitutionAt] =
      querySourceLocation("@") ^^ {
        case (loc, _) =>
          ctx.functionSubstitutionPairAnchor match {
            case None =>
              throw FunctionSubstitutionAtError(loc)
            case Some(anchor) =>
              TLAFunctionSubstitutionAt()
                .setSourceLocation(loc)
                .setRefersTo(anchor)
          }
      }

  def tlaFunctionSubstitutionExpr(implicit ctx: TLAParserContext): Parser[TLAFunctionSubstitution] =
    withSourceLocation {
      val origCtx = ctx
      "[" ~> wsChk ~> tlaExpression ~ (wsChk ~> "EXCEPT" ~>! wsChk ~> tlaComma1Sep {
        withSourceLocation {
          "!" ~>! rep1 {
            wsChk ~> (
              withSourceLocation {
                "." ~> wsChk ~> tlaIdentifierExpr ^^ { id: TLAIdentifier =>
                  TLAFunctionSubstitutionKey(List(TLAString(id.id).setSourceLocation(id.sourceLocation)))
                }
              } |
                withSourceLocation {
                  "[" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ "]" ^^ TLAFunctionSubstitutionKey
                })
          }.flatMap { path =>
            val anchor = TLAFunctionSubstitutionPairAnchor() // definition for the @ expression
              .setSourceLocation(path.view.map(_.sourceLocation).reduce(_ ++ _))
            implicit val ctx: TLAParserContext = origCtx.withFunctionSubstitutionPairAnchor(anchor)
            (wsChk ~> "=" ~> wsChk ~> tlaExpression) ^^ { value =>
              TLAFunctionSubstitutionPair(anchor, path, value)
            }
          }
        }
      } <~ wsChk <~ "]") ^^ {
        case fn ~ pairs => TLAFunctionSubstitution(fn, pairs)
      }
    }

  def tlaQuantifiedExistentialExpr(implicit ctx: TLAParserContext): Parser[TLAQuantifiedExistential] = {
    val origCtx = ctx
    withSourceLocation {
      ("\\E" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound)).flatMap(bounds => {
        implicit val ctx: TLAParserContext = bounds.foldLeft(origCtx)(_.withDefinition(_))
        (wsChk ~> ":" ~>! wsChk ~> tlaExpression) ^^ ((bounds, _))
      }) ^^ {
        case (bounds, predicate) => TLAQuantifiedExistential(bounds, predicate)
      }
    }
  }

  def tlaQuantifiedUniversalExpr(implicit ctx: TLAParserContext): Parser[TLAQuantifiedUniversal] = {
    val origCtx = ctx
    withSourceLocation {
      ("\\A" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound)).flatMap { bounds =>
        implicit val ctx: TLAParserContext = bounds.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((bounds, _))
      } ^^ {
        case (bounds, predicate) => TLAQuantifiedUniversal(bounds, predicate)
      }
    }
  }

  def tlaUnquantifiedExistentialExpr(implicit ctx: TLAParserContext): Parser[TLAExistential] = {
    val origCtx = ctx
    withSourceLocation {
      (("\\EE" | "\\E") ~> wsChk ~> tlaComma1Sep(tlaIdentifierExpr)).map(_.map(_.toDefiningIdentifier)).flatMap { ids =>
        implicit val ctx: TLAParserContext = ids.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((ids, _))
      } ^^ {
        case (ids, predicate) => TLAExistential(ids, predicate)
      }
    }
  }

  def tlaUnquantifiedUniversalExpr(implicit ctx: TLAParserContext): Parser[TLAUniversal] = {
    val origCtx = ctx
    withSourceLocation {
      (("\\AA" | "\\A") ~> wsChk ~> tlaComma1Sep(tlaIdentifierExpr)).map(_.map(_.toDefiningIdentifier)).flatMap { ids =>
        implicit val ctx: TLAParserContext = ids.foldLeft(origCtx)(_.withDefinition(_))
        wsChk ~> ":" ~>! wsChk ~> tlaExpression ^^ ((ids, _))
      } ^^ {
        case (ids, predicate) => TLAUniversal(ids, predicate)
      }
    }
  }

  def tlaSetConstructorExpr(implicit ctx: TLAParserContext): Parser[TLASetConstructor] =
    withSourceLocation {
      "{" ~> wsChk ~> tlaCommaSep(tlaExpression) <~ wsChk <~ "}" ^^ TLASetConstructor
    }

  def tlaSetRefinementExpr(implicit ctx: TLAParserContext): Parser[TLASetRefinement] =
    withSourceLocation {
      val origCtx = ctx
      ("{" ~> wsChk ~> tlaIdentifierOrTupleQuantifierBound <~ wsChk <~ ":").flatMap { binding =>
        implicit val ctx: TLAParserContext = origCtx.withDefinition(binding)
        (wsChk ~> tlaExpression <~ wsChk <~ "}") ^^ ((binding, _))
      } ^^ {
        case (binding, whenExpr) => TLASetRefinement(binding, whenExpr)
      }
    }

  def tlaSetComprehensionExpr(implicit ctx: TLAParserContext): Parser[TLASetComprehension] = {
    val origCtx = ctx
    withSourceLocation {
      ("{" ~> wsChk ~> {
        implicit val ctx: TLAParserContext = origCtx.withLateBinding
        tlaExpression <~ wsChk <~ ":"
      }) ~ (wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "}") ^^ {
        case expr ~ bounds =>
          // extract all late bindings from bounds, and match them up with any relevant elements
          // of lateBindings, removing them in the process
          val defns: List[DefinitionOne] = bounds.flatMap(bind => bind.singleDefinitions)
          val defnMap = defns.view.map(defn => defn.identifier.asInstanceOf[ScopeIdentifierName].name -> defn).toMap

          // gather all nested unbound names
          // (yes, this could end up being really slow, but last time I tried to be smart w/ mutable state or something, a fuzz tester exposed a really weird bug)
          val idents = mutable.ListBuffer[TLAGeneralIdentifier]()
          expr.visit(Visitable.TopDownFirstStrategy) {
            case ident@TLAGeneralIdentifier(_, Nil) if !ident.hasRefersTo => idents += ident
          }

          idents.foreach { ident =>
            defnMap.get(ident.name) match {
              case Some(defn) => ident.setRefersTo(defn)
              case None =>
                // if the late bindings count is 0 after this, we should check that no idents remain unbound.
                // if so, raise the [AST traversal-wise, probably lexically] "earliest" one as an error.
                // otherwise, unbound idents may still be bound via currently unknown context, so don't do anything
                if(ctx.lateBindingStack == 0) {
                  throw DefinitionLookupError(Nil, Definition.ScopeIdentifierName(ident.name))
                }
            }
          }

          TLASetComprehension(expr, bounds)
      }
    }
  }

  def tlaLetExpr(implicit ctx: TLAParserContext): Parser[TLALet] =
    withSourceLocation {
      "LET" ~>! wsChk ~> {
        def impl(pfx: List[TLAUnit with Definition])(implicit ctx: TLAParserContext): Parser[(List[TLAUnit with Definition],TLAExpression)] = {
          val origCtx = ctx
          (tlaOperatorDefinition(isLocal=false) | tlaFunctionDefinition(isLocal=false) | tlaModuleDefinition(isLocal=false)).flatMap { (defn: TLAUnit with Definition) =>
            implicit val ctx: TLAParserContext = origCtx.withDefinition(defn)
            val nextPfx = pfx :+ defn
            wsChk ~> (impl(nextPfx) | (("IN" ~>! wsChk ~> tlaExpression) ^^ ((nextPfx, _))))
          }
        }
        impl(Nil)
      } ^^ {
        case (units, body) => TLALet(units, body)
      }
    }

  def tlaFairnessConstraintExpr(implicit ctx: TLAParserContext): Parser[TLAFairness] =
    withSourceLocation {
      ("WF_" ^^^ TLAFairness.WeakFairness | "SF_" ^^^ TLAFairness.StrongFairness) ~!
        (wsChk ~> tlaExpression) ~!
        (wsChk ~> "(" ~> wsChk ~>! tlaExpression <~ wsChk <~ ")") ^^ {
        case tpe ~ vars ~ expr => TLAFairness(tpe, vars, expr)
      }
    }

  val tlaPrefixOperator: Parser[TLASymbol] =
    withSourceLocation {
      TLAMeta.prefixOperators.keys.toList.sorted.sortWith(_.length > _.length)
        .foldRight(failure("not a prefix operator"): Parser[TLASymbol]) { (pfx, otherwise) =>
          if (pfx == "-_") { // special-case the syntactic anomaly that is "-"
            "-" ^^^ TLASymbol(TLASymbol.forString("-_")) | otherwise
          } else {
            pfx ^^^ TLASymbol(TLASymbol.forString(pfx)) | otherwise
          }
        }
    }

  // same as tlaPrefixOperator, but will read -. instead of just -
  val tlaPrefixOperatorDef: Parser[TLASymbol] =
    withSourceLocation {
      TLAMeta.prefixOperators.keys.toList.sorted.sortWith(_.length > _.length)
        .foldRight(failure("not a prefix operator"): Parser[TLASymbol]) { (pfx, otherwise) =>
          if (pfx == "-_") { // special-case the syntactic anomaly that is "-"
            "-." ^^ (_ => TLASymbol(TLASymbol.forString("-_"))) | otherwise
          } else {
            pfx ^^ (_ => TLASymbol(TLASymbol.forString(pfx))) | otherwise
          }
        }
    }

  private lazy val tlaInfixOperatorV: Parser[TLASymbol] =
    TLAMeta.infixOperators.keys.toList.sorted.sortWith(_.length > _.length)
      .foldRight(failure("not an infix operator"): Parser[TLASymbol]) { (str, otherwise) =>
        str ^^ (_ => TLASymbol(TLASymbol.forString(str))) | otherwise
      }
  def tlaInfixOperator: Parser[TLASymbol] = tlaInfixOperatorV

  val tlaPostfixOperator: Parser[TLASymbol] =
    TLAMeta.postfixOperators.keys.toList.sorted.sortWith(_.length > _.length)
      .foldRight(failure("not a postfix operator"): Parser[TLASymbol]) { (str, otherwise) =>
        str ^^ (_ => TLASymbol(TLASymbol.forString(str))) | otherwise
      }

  def tlaExpressionMinPrecedence(minPrecedence: Int)(implicit ctx: TLAParserContext): Parser[TLAExpression] = {
    val lhsWithPrefix = querySourceLocation(tlaInstancePrefix ~ (wsChk ~> tlaPrefixOperator)).flatMap {
      case (loc, pfx ~ opSym) =>
        val (lowPrec, highPrec) = (opSym.symbol.precedenceLow, opSym.symbol.precedenceHigh)
        wsChk ~> querySourceLocation(tlaExpressionMinPrecedence(highPrec + 1)) ^^ {
          case (loc2, innerExpr) =>
            val result = TLAOperatorCall(Definition.ScopeIdentifierSymbol(opSym), pfx, List(innerExpr))
              .setSourceLocation(loc ++ loc2)
            ctx.lookupDefinition(pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition.ScopeIdentifierSymbol(opSym)) match {
              case None => throw DefinitionLookupError(pfx, Definition.ScopeIdentifierSymbol(opSym))
              case Some(defn) => result.setRefersTo(defn)
            }
            result
        }
    } | tlaExpressionNoOperators

    def withPartOpt(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      withFunctionCall(lhsLoc, lhs, maxPrecedence) | withDot(lhsLoc, lhs, maxPrecedence) |
        withInfix(lhsLoc, lhs, maxPrecedence) | withPostfix(lhsLoc, lhs, maxPrecedence) |
        success(lhs)

    def withPostfix(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      querySourceLocation {
        (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> tlaPostfixOperator) ^? {
          case pfx ~ opSym if opSym.symbol.precedence >= minPrecedence =>
            (pfx, opSym)
        }
      }.flatMap {
        case (loc, (pfx, opSym)) =>
          val combinedLoc = lhsLoc ++ loc
          val result = TLAOperatorCall(Definition.ScopeIdentifierSymbol(opSym), pfx, List(lhs))
            .setSourceLocation(combinedLoc)
          ctx.lookupDefinition(pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition.ScopeIdentifierSymbol(opSym)) match {
            case None => throw DefinitionLookupError(pfx, Definition.ScopeIdentifierSymbol(opSym))
            case Some(defn) => result.setRefersTo(defn)
          }
          withPartOpt(combinedLoc, result, maxPrecedence)
      }

    def withFunctionCall(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      if(minPrecedence <= 16) {
        querySourceLocation("[" ~> wsChk ~> tlaComma1Sep(tlaExpression) <~ wsChk <~ "]").flatMap {
          case (loc, args) =>
            val combinedLoc = lhsLoc ++ loc
            withPartOpt(combinedLoc, TLAFunctionCall(lhs, args).setSourceLocation(combinedLoc), 15)
        }
      } else {
        failure("not at precedence 16")
      }

    def withDot(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      if(minPrecedence <= 17) {
        rep1sep("." ~> wsChk ~> tlaIdentifierExpr, wsChk).flatMap { dots =>
          val (combinedLoc, result) = dots.foldLeft((lhsLoc, lhs)) { (acc, dotId) =>
            val (lhsLoc, lhs) = acc
            val combinedLoc = lhsLoc ++ dotId.sourceLocation
            (combinedLoc, TLADot(lhs, dotId).setSourceLocation(combinedLoc))
          }
          withPartOpt(combinedLoc, result, 16)
        }
      } else {
        failure("not at precedence 17")
      }

    def withInfix(lhsLoc: SourceLocation, lhs: TLAExpression, maxPrecedence: Int): Parser[TLAExpression] =
      querySourceLocation((wsChk ~> tlaInstancePrefix) ~ (wsChk ~> withSourceLocation(tlaInfixOperator)) ^? {
        case pfx ~ opSym if opSym.symbol.precedenceLow >= minPrecedence && opSym.symbol.precedenceHigh <= maxPrecedence =>
          (pfx, opSym)
      }).flatMap {
        case (loc, (pfx, opSym)) =>
          val (lowPrec, highPrec, leftAssoc) = (opSym.symbol.precedenceLow, opSym.symbol.precedenceHigh, opSym.symbol.isAssociative)
          querySourceLocation(wsChk ~> tlaExpressionMinPrecedence(highPrec + 1)).flatMap {
            case (rhsLoc, rhs) =>
              val combinedLoc = lhsLoc ++ loc ++ rhsLoc
              val result = TLAOperatorCall(Definition.ScopeIdentifierSymbol(opSym), pfx, List(lhs, rhs))
                .setSourceLocation(combinedLoc)
              ctx.lookupDefinition(pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition.ScopeIdentifierSymbol(opSym)) match {
                case None => throw DefinitionLookupError(pfx, Definition.ScopeIdentifierSymbol(opSym))
                case Some(defn) => result.setRefersTo(defn)
              }
              if (leftAssoc) {
                def assoc(lhsLoc: SourceLocation, lhs: TLAExpression): Parser[TLAExpression] =
                  querySourceLocation {
                    (wsChk ~> tlaInstancePrefix) ~ (wsChk ~> opSym.symbol) ~ (wsChk ~> tlaExpressionMinPrecedence(highPrec + 1))
                  }.flatMap {
                    case (loc, pfx ~ opSym ~ rhs) =>
                      val combinedLoc = lhsLoc ++ loc
                      val nextLhs = TLAOperatorCall(Definition.ScopeIdentifierSymbol(opSym), pfx, List(lhs, rhs))
                        .setSourceLocation(combinedLoc)
                      ctx.lookupDefinition(pfx.map(id => Definition.ScopeIdentifierName(id.id)) :+ Definition.ScopeIdentifierSymbol(opSym)) match {
                        case None => throw DefinitionLookupError(pfx, Definition.ScopeIdentifierSymbol(opSym))
                        case Some(defn) => nextLhs.setRefersTo(defn)
                      }
                      assoc(combinedLoc, nextLhs) | withPartOpt(combinedLoc, nextLhs, lowPrec-1)
                  }
                assoc(combinedLoc, result) | withPartOpt(combinedLoc, result, lowPrec - 1)
              } else {
                withPartOpt(combinedLoc, result, lowPrec - 1)
              }
          }
      }

    querySourceLocation(lhsWithPrefix).flatMap { case (loc, lhs) => withPartOpt(loc, lhs, 18) }
  }

  def tlaExpressionNoOperators(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaNumberExpr |
      tlaStringExpr |
      ("(" ~>! wsChk ~> tlaExpression <~ wsChk <~ ")") |
      tlaFunctionSubstitutionAtExpr |
      tlaTupleExpr |
      tlaRequiredActionExpr |
      tlaOperatorCallOrGeneralIdentifier |
      tlaFairnessConstraintExpr |
      tlaConjunctExpr | tlaDisjunctExpr |
      tlaIfExpr |
      tlaLetExpr |
      tlaCaseExpr |
      // starting with [
      tlaFunctionExpr | tlaRecordSetExpr | tlaRecordConstructorExpr | tlaFunctionSetExpr |
      tlaMaybeActionExpr | tlaFunctionSubstitutionExpr |
      // starting with \E, EE, \A, \AA
      tlaQuantifiedExistentialExpr | tlaQuantifiedUniversalExpr |
      tlaUnquantifiedExistentialExpr | tlaUnquantifiedUniversalExpr |
      // starting with {
      tlaSetRefinementExpr | tlaSetComprehensionExpr | tlaSetConstructorExpr

  def tlaExpression(implicit ctx: TLAParserContext): Parser[TLAExpression] =
    tlaExpressionMinPrecedence(0)

  def tlaOpDecl(implicit ctx: TLAParserContext): Parser[TLAOpDecl] =
    withSourceLocation {
      val named = tlaIdentifierExpr ~ (wsChk ~> "(" ~> tlaComma1Sep("_") <~ wsChk <~ ")") ^^ {
        case id ~ args => TLAOpDecl.NamedVariant(id, args.length)
      }
      val id = tlaIdentifierExpr ^^ (TLAOpDecl.NamedVariant(_, 0))
      val prefix = tlaPrefixOperatorDef <~ wsChk <~ "_" ^^ TLAOpDecl.SymbolVariant
      val infix = "_" ~> wsChk ~> tlaInfixOperator <~ wsChk <~ "_" ^^ TLAOpDecl.SymbolVariant
      val postfix = "_" ~> wsChk ~> tlaPostfixOperator ^^ TLAOpDecl.SymbolVariant

      (named | id | prefix | infix | postfix) ^^ (TLAOpDecl(_))
    }

  def tlaOperatorDefinition(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAOperatorDefinition] = {
    val origCtx = ctx
    val prefix = withSourceLocation {
      (tlaPrefixOperatorDef ~ (wsChk ~> tlaIdentifierExpr)).flatMap {
        case opSym ~ id =>
          val opDecl = TLAOpDecl(TLAOpDecl.NamedVariant(id, 0)).setSourceLocation(id.sourceLocation)
          implicit val ctx: TLAParserContext = origCtx.withDefinition(opDecl)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((opSym, opDecl, _))
      } ^^ {
        case (opSym, opDecl, body) =>
          TLAOperatorDefinition(Definition.ScopeIdentifierSymbol(opSym), List(opDecl), body, isLocal)
      }
    }
    val infix = withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> tlaInfixOperator) ~ (wsChk ~> tlaIdentifierExpr)).flatMap {
        case lhsId ~ opSym ~ rhsId =>
          val lhsOpDecl = TLAOpDecl(TLAOpDecl.NamedVariant(lhsId, 0)).setSourceLocation(lhsId.sourceLocation)
          val rhsOpDecl = TLAOpDecl(TLAOpDecl.NamedVariant(rhsId, 0)).setSourceLocation(rhsId.sourceLocation)
          implicit val ctx: TLAParserContext = origCtx.withDefinition(lhsOpDecl).withDefinition(rhsOpDecl)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((lhsOpDecl, opSym, rhsOpDecl, _))
      } ^^ {
        case (lhsOpDecl, opSym, rhsOpDecl, body) =>
          TLAOperatorDefinition(Definition.ScopeIdentifierSymbol(opSym), List(lhsOpDecl, rhsOpDecl), body, isLocal)
      }
    }
    val postfix = withSourceLocation {
      (tlaIdentifierExpr ~ (wsChk ~> tlaPostfixOperator)).flatMap {
        case id ~ opSym =>
          val opDecl = TLAOpDecl(TLAOpDecl.NamedVariant(id, 0)).setSourceLocation(id.sourceLocation)
          implicit val ctx: TLAParserContext = origCtx.withDefinition(opDecl)
          (wsChk ~> "==" ~> wsChk ~> tlaExpression) ^^ ((opDecl, opSym, _))
      } ^^ {
        case (opDecl, opSym, body) =>
          TLAOperatorDefinition(Definition.ScopeIdentifierSymbol(opSym), List(opDecl), body, isLocal)
      }
    }
    val nonfix = withSourceLocation {
      (tlaIdentifierExpr ~ opt(wsChk ~> "(" ~> tlaComma1Sep(tlaOpDecl) <~ wsChk <~ ")") <~ wsChk <~ "==" <~ wsChk).flatMap {
        case id ~ None => tlaExpression ^^ ((id, Nil, _))
        case id ~ Some(opDecls) =>
          implicit val ctx: TLAParserContext = opDecls.foldLeft(origCtx)(_.withDefinition(_))
          tlaExpression ^^ ((id, opDecls, _))
      } ^^ {
        case (id, opDecls, body) =>
          TLAOperatorDefinition(Definition.ScopeIdentifierName(id), opDecls, body, isLocal)
      }
    }

    prefix | infix | postfix | nonfix
  }

  def tlaFunctionDefinition(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAOperatorDefinition] = {
    val origCtx = ctx
    withSourceLocation {
      tlaIdentifierExpr ~ withSourceLocation {
        (wsChk ~> "[" ~> wsChk ~> tlaComma1Sep(tlaQuantifierBound) <~ wsChk <~ "]" <~ wsChk <~ "==").flatMap { bounds =>
          implicit val ctx: TLAParserContext = bounds.foldLeft(origCtx)(_.withDefinition(_))
          (wsChk ~> tlaExpression) ^^ (TLAFunction(bounds, _))
        }
      } ^^ {
        case id ~ function => TLAOperatorDefinition(Definition.ScopeIdentifierName(id), Nil, function, isLocal)
      }
    }
  }

  def tlaInstance(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAInstance] =
    withSourceLocation {
      "INSTANCE" ~> wsChk ~> tlaIdentifierExpr ~
        opt(wsChk ~> "WITH" ~> tlaComma1Sep(
          withSourceLocation {
            (tlaIdentifierExpr.map(Definition.ScopeIdentifierName) | (tlaPrefixOperatorDef | tlaInfixOperator | tlaPostfixOperator).map(Definition.ScopeIdentifierSymbol)) ~
              (wsChk ~> "<-" ~> wsChk ~> tlaExpression) ^^ {
              case from ~ to => TLAInstanceRemapping(from, to)
            }
          })).map(_.getOrElse(Nil)) ^^ {
        case moduleId ~ substitutions =>
          // TODO: load the module data
          TLAInstance(moduleId, substitutions, isLocal)
      }
    }

  def tlaModuleDefinition(isLocal: Boolean)(implicit ctx: TLAParserContext): Parser[TLAModuleDefinition] =
    withSourceLocation {
      val origCtx = ctx
      (tlaIdentifierExpr ~ opt(wsChk ~> "(" ~> tlaComma1Sep(tlaOpDecl) <~ wsChk <~ ")")).flatMap {
        case id ~ argsOpt =>
          implicit val ctx: TLAParserContext = argsOpt.getOrElse(Nil).foldLeft(origCtx)(_.withDefinition(_))
          (wsChk ~> "==" ~> wsChk ~> tlaInstance(isLocal)) ^^ ((id, argsOpt.getOrElse(Nil), _))
      } ^^ {
        case (id, args, instance) => TLAModuleDefinition(id, args, instance, isLocal)
      }
    }

  def tlaModule(implicit ctx: TLAParserContext): Parser[TLAModule] =
    withSourceLocation {
      val origCtx = ctx
      ("----" ~> rep(elem('-')) ~> wsChk ~> "MODULE" ~>! wsChk ~> tlaIdentifierExpr <~ wsChk <~ "----" <~ rep(elem('-')) <~ wsChk) ~
        opt("EXTENDS" ~>! wsChk ~> tlaComma1Sep(tlaIdentifierExpr) <~ wsChk).flatMap { exts =>
          def unitRec(implicit ctx: TLAParserContext): Parser[List[TLAUnit]] = {
            val origCtx = ctx
            opt("----" ~> rep(elem('-')) ~> wsChk) ~> tlaUnit.flatMap { unit =>
              implicit val ctx: TLAParserContext = unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
              (wsChk ~> unitRec ^^ (unit :: _)) | success(List(unit))
            }
          }
          val extensions = exts.getOrElse(Nil).map(ext => origCtx.lookupModuleExtends(Definition.ScopeIdentifierName(ext)))
          implicit val ctx: TLAParserContext = extensions.foldLeft(origCtx) { (ctx, ext) => ext.singleDefinitions.foldLeft(ctx)(_.withDefinition(_)) }
          (unitRec | success(Nil)) ^^ ((extensions, _))
        } <~ wsChk <~ "====" <~ rep(elem('=')) ^^ {
        case name ~ ((exts, units)) => TLAModule(name, exts, units)
      }
    }

  def tlaUnit(implicit ctx: TLAParserContext): Parser[TLAUnit] = {
    val variableDeclaration: Parser[TLAUnit] = withSourceLocation {
      ("VARIABLES" | "VARIABLE") ~>! wsChk ~> tlaComma1Sep(tlaIdentifierExpr.map(_.toDefiningIdentifier)) ^^ TLAVariableDeclaration
    }
    val constantDeclaration: Parser[TLAUnit] = withSourceLocation {
      ("CONSTANTS" | "CONSTANT") ~>! wsChk ~> tlaComma1Sep(tlaOpDecl) ^^ TLAConstantDeclaration
    }
    val assumption: Parser[TLAUnit] = withSourceLocation {
      ("ASSUME" | "ASSUMPTION" | "AXIOM") ~>! wsChk ~> tlaExpression ^^ TLAAssumption
    }
    val theorem: Parser[TLAUnit] = withSourceLocation {
      "THEOREM" ~>! wsChk ~> tlaExpression ^^ TLATheorem
    }

    ("LOCAL" ~>! wsChk ~> {
        tlaInstance(true) | tlaModuleDefinition(true) | tlaFunctionDefinition(true) |
          tlaOperatorDefinition(true)
      }) |
      tlaInstance(false) |
      tlaModuleDefinition(false) |
      tlaFunctionDefinition(false) |
      tlaOperatorDefinition(false) |
      variableDeclaration |
      constantDeclaration |
      assumption |
      theorem |
      tlaModule
  }

  val findTLAModule: Parser[Unit] =
    rep(not("----") ~> anything) ^^^ ()

  def tlaModuleBeforeTranslation(implicit ctx: TLAParserContext): Parser[TLAModule] =
    withSourceLocation {
      val translationTag = ("\\*" <~ rep("*") <~ rep1(" ") <~ "BEGIN" <~ rep1(" ") <~ "TRANSLATION")
        .withFailureMessage("\\* expected: for scoping reasons, an MPCal-compilable TLA+ module must contain a `\\* BEGIN TRANSLATION` tag")
      val wsWithoutTranslationTag =
        rep(regex("""\s+""".r) | tlaMultilineComment | not(translationTag) ~> tlaLineComment)

      val origCtx = ctx
      ("----" ~> rep(elem('-')) ~> wsChk ~> "MODULE" ~>! wsChk ~> tlaIdentifierExpr <~ wsChk <~ "----" <~ rep(elem('-'))) ~
        opt(wsChk ~> "EXTENDS" ~>! wsChk ~> tlaComma1Sep(tlaIdentifierExpr) <~ wsWithoutTranslationTag).flatMap { exts =>
          def unitRec(implicit ctx: TLAParserContext): Parser[List[TLAUnit]] = {
            val origCtx = ctx
            opt("----" ~> rep(elem('-')) ~> wsWithoutTranslationTag) ~> tlaUnit.flatMap { unit =>
              implicit val ctx: TLAParserContext = unit.definitions.foldLeft(origCtx)(_.withDefinition(_))
              (wsWithoutTranslationTag ~> unitRec ^^ (unit :: _)) | success(List(unit))
            }
          }
          val extensions = exts.getOrElse(Nil).map(ext => origCtx.lookupModuleExtends(Definition.ScopeIdentifierName(ext)))
          implicit val ctx: TLAParserContext = extensions.foldLeft(origCtx) { (ctx, ext) => ext.singleDefinitions.foldLeft(ctx)(_.withDefinition(_)) }
          (unitRec | success(Nil)) ^^ ((extensions, _))
        } <~ wsWithoutTranslationTag <~ translationTag ^^ {
        case name ~ ((exts, units)) => TLAModule(name, exts, units)
      }
    }
}

object TLAParser extends TLAParser with ParsingUtils {
  def readExpression(underlying: SourceLocation.UnderlyingText, seq: CharSequence, definitions: Seq[Definition] = Nil): TLAExpression = {
    implicit val ctx: TLAParserContext = definitions.foldLeft(
      BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_)))(_.withDefinition(_))
    checkResult {
      phrase(wsChk ~> tlaExpression <~ wsChk)(buildReader(seq, underlying))
    }
  }

  def readModule(underlying: SourceLocation.UnderlyingText, seq: CharSequence): TLAModule = {
    implicit val ctx: TLAParserContext =
      BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_))
    checkResult(phrase(
      findTLAModule ~> tlaModule <~ rep(accept("anything", { case _ => () })))(buildReader(seq, underlying)))
  }

  def readModuleBeforeTranslation(underlying: SourceLocation.UnderlyingText, seq: CharSequence): TLAModule = {
    implicit val ctx: TLAParserContext =
      BuiltinModules.Intrinsics.members.foldLeft(TLAParserContext())(_.withDefinition(_))
    checkResult(phrase(
      findTLAModule ~> tlaModuleBeforeTranslation <~ rep(accept("anything", { case _ => () })))(buildReader(seq, underlying)))
  }
}
