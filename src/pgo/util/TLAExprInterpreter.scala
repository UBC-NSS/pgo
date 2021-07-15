package pgo.util

import pgo.model.{Definition, DefinitionOne, RefersTo, SourceLocation}
import pgo.model.tla._
import pgo.parser.TLAParser
import pgo.util.Unreachable.!!!

import scala.annotation.tailrec

object TLAExprInterpreter {
  final case class Unsupported() extends RuntimeException("unsupported")
  final case class TypeError() extends RuntimeException("TLA+ type error")

  sealed abstract class TLAValue
  object TLAValue {
    def parseFromString(str: String): TLAValue = {
      val expr = TLAParser.readExpression(
        new SourceLocation.UnderlyingString(str),
        str,
        // Integers needed for prefix `-`, and TLC needed for `:>` and `@@`
        definitions = BuiltinModules.Integers.members ::: BuiltinModules.TLC.members)
      interpret(expr)(Map.empty)
    }
  }

  final case class TLAValueBool(value: Boolean) extends TLAValue
  final case class TLAValueNumber(value: Int) extends TLAValue
  final case class TLAValueString(value: String) extends TLAValue
  final case class TLAValueSet(value: Set[TLAValue]) extends TLAValue
  final case class TLAValueTuple(value: Vector[TLAValue]) extends TLAValue
  final case class TLAValueFunction(value: Map[TLAValue,TLAValue]) extends TLAValue

  lazy val builtinOperators: IdMap[DefinitionOne,List[TLAValue]=>TLAValue] =
    IdMap(
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalAndSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(lhs && rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalOrSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalNotSymbol) -> {
        case List(TLAValueBool(op)) => TLAValueBool(!op)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.ImpliesSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(!lhs || rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EquivSymbol) -> {
        case List(TLAValueBool(lhs), TLAValueBool(rhs)) => TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberAlpha("TRUE") -> {
        case Nil => TLAValueBool(true)
      },
      BuiltinModules.Intrinsics.memberAlpha("FALSE") -> {
        case Nil => TLAValueBool(false)
      },
      BuiltinModules.Intrinsics.memberAlpha("BOOLEAN") -> {
        case Nil => TLAValueSet(Set(TLAValueBool(true), TLAValueBool(false)))
      },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.EqualsSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueBool(lhs == rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.NotEqualsSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueBool(lhs != rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.InSymbol) -> {
        case List(lhs, TLAValueSet(rhs)) => TLAValueBool(rhs.contains(lhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.NotInSymbol) -> {
        case List(lhs, TLAValueSet(rhs)) => TLAValueBool(!rhs.contains(lhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.IntersectSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs & rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.UnionSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs | rhs)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.SubsetOrEqualSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueBool(lhs.subsetOf(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.BackslashSymbol) -> {
        case List(TLAValueSet(lhs), TLAValueSet(rhs)) => TLAValueSet(lhs.diff(rhs))
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) => TLAValueSet(set.subsets().map(TLAValueSet).toSet)
      },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrefixUnionSymbol) -> {
        case List(TLAValueSet(set)) =>
          TLAValueSet(set.view.map {
            case TLAValueSet(memberSet) => memberSet
          }.foldLeft(Set.empty[TLAValue])(_ | _))
      },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.DomainSymbol) -> {
        case List(TLAValueFunction(fn)) => TLAValueSet(fn.keySet)
      },

      BuiltinModules.Intrinsics.memberAlpha("STRING") -> { case Nil => throw Unsupported() },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.PrimeSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.EnabledSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.UnchangedSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.CDotSymbol) -> { _ => throw Unsupported() },

      BuiltinModules.Intrinsics.memberSym(TLASymbol.TLAlwaysSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.TLEventuallySymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.SequencingSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Intrinsics.memberSym(TLASymbol.PlusArrowSymbol) -> { _ => throw Unsupported() },

      BuiltinModules.TLC.memberAlpha("Print") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("PrintT") -> { case List(_) => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("Assert") -> {
        case List(TLAValueBool(cond), out) =>
          assert(cond, out.toString)
          TLAValueBool(true)
      },
      BuiltinModules.TLC.memberAlpha("JavaTime") -> { case Nil => throw Unsupported() },
      BuiltinModules.TLC.memberSym(TLASymbol.ColonGreaterThanSymbol) -> {
        case List(lhs, rhs) => TLAValueFunction(Map(lhs -> rhs))
      },
      BuiltinModules.TLC.memberSym(TLASymbol.DoubleAtSignSymbol) -> {
        case List(TLAValueFunction(lhs), TLAValueFunction(rhs)) => TLAValueFunction(lhs ++ rhs)
      },
      BuiltinModules.TLC.memberAlpha("Permutations") -> { _ => throw Unsupported() },
      BuiltinModules.TLC.memberAlpha("SortSeq") -> { _ => throw Unsupported() },

      BuiltinModules.Sequences.memberAlpha("Seq") -> {
        case List(TLAValueSet(elems)) =>
          TLAValueSet(elems.toVector.permutations.map(TLAValueTuple).toSet)
      },
      BuiltinModules.Sequences.memberAlpha("Len") -> {
        case List(TLAValueTuple(elems)) => TLAValueNumber(elems.size)
      },
      BuiltinModules.Sequences.memberSym(TLASymbol.OSymbol) -> {
        case List(TLAValueTuple(lhs), TLAValueTuple(rhs)) => TLAValueTuple(lhs ++ rhs)
      },
      BuiltinModules.Sequences.memberAlpha("Append") -> {
        case List(TLAValueTuple(elems), elem) => TLAValueTuple(elems :+ elem)
      },
      BuiltinModules.Sequences.memberAlpha("Head") -> {
        case List(TLAValueTuple(elems)) =>
          require(elems.nonEmpty)
          elems.head
      },
      BuiltinModules.Sequences.memberAlpha("Tail") -> {
        case List(TLAValueTuple(elems)) =>
          require(elems.nonEmpty)
          TLAValueTuple(elems.tail)
      },
      BuiltinModules.Sequences.memberAlpha("SubSeq") -> {
        case List(TLAValueTuple(elems), TLAValueNumber(from), TLAValueNumber(to)) =>
          TLAValueTuple(elems.slice(from, to + 1))
      },
      BuiltinModules.Sequences.memberAlpha("SelectSeq") -> { _ => throw Unsupported() },

      BuiltinModules.FiniteSets.memberAlpha("IsFiniteSet") -> {
        case List(TLAValueSet(_)) => TLAValueBool(true)
      },
      BuiltinModules.FiniteSets.memberAlpha("Cardinality") -> {
        case List(TLAValueSet(set)) => TLAValueNumber(set.size)
      },

      BuiltinModules.Bags.memberAlpha("IsABag") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagToSet") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("SetToBag") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagIn") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("EmptyBag") -> { case Nil => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("CopiesIn") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.Bags.memberSym(TLASymbol.OPlusSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Bags.memberSym(TLASymbol.OMinusSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagUnion") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberSym(TLASymbol.SquareSupersetOrEqualSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("SubBag") -> { case List(_) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagOfAll") -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.Bags.memberAlpha("BagCardinality") -> { case List(_) => throw Unsupported() },

      BuiltinModules.Peano.memberAlpha("PeanoAxioms") -> { case List(_, _, _) => throw Unsupported() },
      BuiltinModules.Peano.memberAlpha("Succ") -> { case Nil => throw Unsupported() },
      BuiltinModules.Peano.memberAlpha("Nat") -> { case Nil => throw Unsupported() },
      BuiltinModules.Peano.memberAlpha("Zero") -> { case Nil => TLAValueNumber(0) },

      BuiltinModules.ProtoReals.memberAlpha("IsModelOfReals") -> { case List(_, _, _, _) => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("RM") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("Real") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("Infinity") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("MinusInfinity") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.PlusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.addExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.AsteriskSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.multiplyExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.LessThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs <= rhs)
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.MinusSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.subtractExact(lhs, rhs))
      },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SlashSymbol) -> { case List(_, _) => throw Unsupported() },
      BuiltinModules.ProtoReals.memberAlpha("Int") -> { case Nil => throw Unsupported() },
      BuiltinModules.ProtoReals.memberSym(TLASymbol.SuperscriptSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueNumber(math.pow(lhs, rhs).toInt)
      },

      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanOrEqualSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs >= rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.LessThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs < rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.GreaterThanSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) => TLAValueBool(lhs > rhs)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DotDotSymbol) -> {
        case List(TLAValueNumber(from), TLAValueNumber(until)) =>
          TLAValueSet((from to until).view.map(TLAValueNumber).toSet)
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.DivSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          require(rhs != 0)
          TLAValueNumber(math.floorDiv(lhs, rhs))
      },
      BuiltinModules.Naturals.memberSym(TLASymbol.PercentSymbol) -> {
        case List(TLAValueNumber(lhs), TLAValueNumber(rhs)) =>
          require(rhs != 0)
          TLAValueNumber(math.floorMod(lhs, rhs))
      },

      BuiltinModules.Integers.memberAlpha("Int") -> { _ => throw Unsupported() },
      BuiltinModules.Integers.memberSym(TLASymbol.NegationSymbol) -> {
        case List(TLAValueNumber(num)) => TLAValueNumber(-num)
      },

      BuiltinModules.Reals.memberAlpha("Real") -> { _ => throw Unsupported() },
      BuiltinModules.Reals.memberSym(TLASymbol.SlashSymbol) -> { _ => throw Unsupported() },
      BuiltinModules.Reals.memberAlpha("Infinity") -> { _ => throw Unsupported() },
    )

  def interpret(expr: TLAExpression)(implicit env: Map[RefersTo.HasReferences,TLAValue]): TLAValue = {
    try {
      expr match {
        case TLAString(value) => TLAValueString(value)
        case TLANumber(value, _) =>
          value match {
            case TLANumber.IntValue(value) => TLAValueNumber(value.intValue)
          }
        case ident@TLAGeneralIdentifier(name, prefix) =>
          assert(prefix.isEmpty)
          env.getOrElse(ident.refersTo, {
            builtinOperators(ident.refersTo)(Nil)
          })
        case TLADot(lhs, identifier) =>
          interpret(lhs) match {
            case TLAValueFunction(value) =>
              val idx = TLAValueString(identifier.id)
              require(value.contains(idx))
              value(idx)
          }
        case opcall@TLAOperatorCall(_, _, arguments) =>
          opcall.refersTo match {
            case builtin: BuiltinModules.TLABuiltinOperator =>
              builtinOperators(builtin)(arguments.map(interpret))
            case TLAOperatorDefinition(_, args, body, _) =>
              require(args.size == arguments.size)
              require(args.forall(_.variant.isInstanceOf[TLAOpDecl.NamedVariant]))
              val argValues = arguments.map(interpret)
              interpret(body)(env = env ++ (args zip argValues))
          }
        case TLAIf(cond, tval, fval) =>
          interpret(cond) match {
            case TLAValueBool(value) =>
              if (value) interpret(tval) else interpret(fval)
          }
        case TLALet(defs, body) =>
          @tailrec
          def impl(defs: List[TLAUnit])(implicit env: Map[RefersTo.HasReferences, TLAValue]): TLAValue =
            defs match {
              case Nil => interpret(body)
              case unit :: restUnits =>
                unit match {
                  case defn@TLAOperatorDefinition(name, args, body, _) if args.isEmpty =>
                    impl(restUnits)(env = env.updated(defn, interpret(body)))
                  case _: TLAOperatorDefinition =>
                    // for definitions with args, they will be called by TLAOperatorCall, and scoping is done already
                    impl(restUnits)
                }
            }

          impl(defs)
        case TLACase(arms, other) =>
          @tailrec
          def armEval(arms: List[TLACaseArm]): TLAValue =
            arms match {
              case Nil => other match {
                case Some(value) => interpret(value)
              }
              case TLACaseArm(cond, result) :: otherArms =>
                interpret(cond) match {
                  case TLAValueBool(value) =>
                    if (value) {
                      interpret(result)
                    } else {
                      armEval(otherArms)
                    }
                }
            }

          armEval(arms)
        case TLAFunction(args, body) =>
          val argSets = args.view.map(_.set).map(interpret).map {
            case TLAValueSet(set) => set
          }.toList

          def impl(args: List[TLAQuantifierBound], argSets: List[Set[TLAValue]], acc: Vector[TLAValue])(implicit env: Map[RefersTo.HasReferences, TLAValue]): Iterator[(TLAValue, TLAValue)] =
            (args, argSets) match {
              case (Nil, Nil) => Iterator.single(TLAValueTuple(acc) -> interpret(body))
              case (TLAQuantifierBound(tpe, ids, _) :: restArgs, argSet :: restArgSets) =>
                  tpe match {
                    case TLAQuantifierBound.IdsType =>
                      val List(id) = ids
                      argSet.iterator.flatMap { v =>
                        impl(restArgs, restArgSets, acc :+ v)(env = env.updated(id, v))
                      }
                    case TLAQuantifierBound.TupleType =>
                      argSet.iterator.flatMap {
                        case v@TLAValueTuple(elems) =>
                          require(elems.size == ids.size)
                          impl(restArgs, restArgSets, acc :+ v)(env = env ++ (ids.view zip elems))
                      }
                  }
            }

          TLAValueFunction(impl(args, argSets, Vector.empty).toMap)
        case TLAFunctionCall(function, params) =>
          val paramValue = params match {
            case List(singleParam) => interpret(singleParam)
            case params => TLAValueTuple(params.view.map(interpret).toVector)
          }
          interpret(function) match {
            case TLAValueTuple(value) =>
              paramValue match {
                case TLAValueNumber(idx) => value(idx)
              }
            case TLAValueFunction(value) => value(paramValue)
          }
        case TLAFunctionSet(from, to) =>
          (interpret(from), interpret(to)) match {
            case (TLAValueSet(fromSet), TLAValueSet(toSet)) =>
              TLAValueSet {
                val keyList = fromSet.toList
                val valueList = toSet.toList
                val valueSets = keyList.iterator.foldLeft(Iterator.single(Nil: List[TLAValue])) { (acc, _) =>
                  acc.flatMap(lst => valueList.iterator.map(v => v :: lst))
                }
                valueSets.map(valueSet => TLAValueFunction((keyList zip valueSet).toMap)).toSet
              }
          }
        case TLAFunctionSubstitution(source, substitutions) =>
          substitutions.foldLeft(interpret(source)) { (fnValue, sub) =>
            val TLAFunctionSubstitutionPair(anchor, keys, value) = sub

            def subKeys(keys: List[TLAFunctionSubstitutionKey], origValue: TLAValue): TLAValue =
              keys match {
                case Nil => interpret(value)(env = env.updated(anchor, origValue))
                case TLAFunctionSubstitutionKey(indices) :: restKeys =>
                  val indexValue = indices match {
                    case List(index) => interpret(index)
                    case indices => TLAValueTuple(indices.view.map(interpret).toVector)
                  }
                  origValue match {
                    case TLAValueFunction(origFn) =>
                      require(origFn.contains(indexValue))
                      TLAValueFunction(origFn.updated(indexValue, subKeys(restKeys, origFn(indexValue))))
                  }
              }

            subKeys(keys, fnValue)
          }
        case at@TLAFunctionSubstitutionAt() => env(at.refersTo)
        case expr@(TLAQuantifiedExistential(_, _) | TLAQuantifiedUniversal(_, _)) =>
          // merge universal and existential code paths, because they are so similar
          val (bounds, body) = expr match {
            case TLAQuantifiedUniversal(bounds, body) => (bounds, body)
            case TLAQuantifiedExistential(bounds, body) => (bounds, body)
          }

          val boundValues = bounds.view.map(_.set).map(interpret).map {
            case TLAValueSet(set) => set // require all sets to be actual sets
          }.toList

          // a function that slots in at the decision point, choosing exists or forall aggregation
          val fn: (Set[TLAValue],TLAValue=>Boolean)=>Boolean = expr match {
            case TLAQuantifiedUniversal(_, _) => _.forall(_)
            case TLAQuantifiedExistential(_, _) => _.exists(_)
          }

          def impl(bounds: List[TLAQuantifierBound], boundValues: List[Set[TLAValue]], envAcc: Map[RefersTo.HasReferences,TLAValue]): Boolean =
            (bounds, boundValues) match {
              case (Nil, Nil) =>
                implicit val env: Map[RefersTo.HasReferences,TLAValue] = envAcc
                interpret(body) match {
                  case TLAValueBool(value) => value
                }
              case (TLAQuantifierBound(tpe, ids, _) :: restBounds, set :: restBoundValues) =>
                tpe match {
                  case TLAQuantifierBound.IdsType =>
                    val List(id) = ids
                    fn(set, v => impl(restBounds, restBoundValues, envAcc.updated(id, v)))
                  case TLAQuantifierBound.TupleType =>
                    fn(set, {
                      case TLAValueTuple(elems) =>
                        require(ids.size == elems.size)
                        impl(restBounds, restBoundValues, envAcc ++ (ids.view zip elems))
                    })
                }
              case _ => !!!
            }

          TLAValueBool(impl(bounds, boundValues, env))
        case TLASetConstructor(contents) =>
          TLAValueSet(contents.view.map(interpret).toSet)
        case TLASetRefinement(TLAQuantifierBound(tpe, ids, set), when) =>
          interpret(set) match {
            case TLAValueSet(setValue) =>
              tpe match {
                case TLAQuantifierBound.IdsType =>
                  val List(id) = ids
                  TLAValueSet(setValue.filter { v =>
                    interpret(when)(env = env.updated(id, v)) match {
                      case TLAValueBool(value) => value
                    }
                  })
                case TLAQuantifierBound.TupleType =>
                  TLAValueSet(setValue.filter {
                    case TLAValueTuple(elems) =>
                      require(elems.size == ids.size)
                      interpret(when)(env = env ++ (ids.view zip elems)) match {
                        case TLAValueBool(value) => value
                      }
                  })
              }
          }
        case TLASetComprehension(body, bounds) =>
          val boundValues = bounds.view.map(_.set).map(interpret).map {
            case TLAValueSet(set) => set // require all sets are actual sets
          }.toList
          def impl(bounds: List[TLAQuantifierBound], boundValues: List[Set[TLAValue]])(implicit env: Map[RefersTo.HasReferences, TLAValue]): Iterator[TLAValue] =
            (bounds, boundValues) match {
              case (Nil, Nil) => Iterator.single(interpret(body))
              case (TLAQuantifierBound(tpe, ids, _) :: restBounds, setValue :: restSetValues) =>
                tpe match {
                  case TLAQuantifierBound.IdsType =>
                    val List(id) = ids
                    setValue.iterator.flatMap { v =>
                      impl(restBounds, restSetValues)(env = env.updated(id, v))
                    }
                  case TLAQuantifierBound.TupleType =>
                    setValue.iterator.flatMap {
                      case TLAValueTuple(elems) =>
                        require(ids.size == elems.size)
                        impl(restBounds, restSetValues)(env = env ++ (ids.view zip elems))
                    }
                }
              case _ => !!!
            }

          TLAValueSet(impl(bounds, boundValues).toSet)
        case TLATuple(elements) =>
          TLAValueTuple(elements.view.map(interpret).toVector)
        case TLARecordConstructor(fields) =>
          TLAValueFunction(fields.view.map {
            case TLARecordConstructorField(name, value) =>
              TLAValueString(name.id) -> interpret(value)
          }.toMap)
        case TLARecordSet(fields) =>
          def impl(fields: List[(String,TLAValue)], acc: Map[TLAValue, TLAValue]): Iterator[TLAValue] =
            fields match {
              case Nil => Iterator.single(TLAValueFunction(acc))
              case (name, TLAValueSet(set)) :: restFields =>
                  set.iterator.flatMap { v =>
                    impl(restFields, acc.updated(TLAValueString(name), v))
                  }
            }

          TLAValueSet(impl(fields.map {
            case TLARecordSetField(name, set) =>
              (name.id, interpret(set))
          }, Map.empty).toSet)
      }
    } catch {
      case err: IllegalArgumentException =>
        throw TypeError().initCause(err)
      case err: MatchError =>
        throw TypeError().initCause(err)
    }
  }
}
