package pgo

import org.scalacheck.Gen
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks
import pgo.model.Definition.ScopeIdentifierName
import pgo.model.DefinitionOne
import pgo.model.tla._
import pgo.trans.PCalRenderPass
import pgo.util.Description._
import pgo.util.TLAExprInterpreter.TLAValue
import pgo.util.{IdSet, TLAExprInterpreter}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.math
import scala.util.control.NonFatal

class TLAExpressionFuzzTests extends AnyFunSuite with ScalaCheckPropertyChecks {
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(workers = 1, minSuccessful = 100, maxDiscardedFactor = 10)

  test("TLA+ expr eval (true random ASTs)") {
    val workDir = os.temp.dir()
    val testFile = workDir / "TestBed.tla"
    val outFile = workDir / "testbed.go"
    var degenerateCases = 0
    var cases = 0

    val modFile = workDir / "go.mod"
    os.write(modFile,
      s"""module example.org/testbed
         |
         |go 1.14
         |
         |replace github.com/UBC-NSS/pgo/distsys => ${os.pwd / "distsys"}
         |
         |require github.com/UBC-NSS/pgo/distsys v0.0.0-00010101000000-000000000000
         |""".stripMargin)

    val mainFile = workDir / "main" / "main.go"
    os.makeDir(workDir / "main")
    os.write(mainFile,
      s"""package main
         |
         |import "github.com/UBC-NSS/pgo/distsys"
         |import "example.org/testbed"
         |
         |type dummyDurableStorage struct{}
         |
         |var _ distsys.MPCalDurableStorage = &dummyDurableStorage{}
         |
         |func (d dummyDurableStorage) RecoverResources() (rec *distsys.MPCalDurableStorageRecord, err error) {
         |	return nil, nil
         |}
         |
         |func (d dummyDurableStorage) SnapshotResources(rec *distsys.MPCalDurableStorageRecord) {
         |	// pass
         |}
         |
         |func main() {
         |  ctx, err := distsys.NewMPCalContext(&dummyDurableStorage{})
         |  if err != nil {
         |    panic(err)
         |  }
         |  err = testbed.TestBed(ctx, distsys.NewTLAString("self"), testbed.Constants{})
         |  if err != nil {
         |    panic(err)
         |  }
         |}""".stripMargin)

    try {
      forAll(trueRandomExprGen) { (expr: TLAExpression) =>
        val mpcalSetup =
          d"----MODULE TestBed----\n" +
            d"EXTENDS Integers, Sequences, TLC, FiniteSets\n" +
            d"(* --mpcal TestBed {\n" +
            d"archetype TestBed() {\n" +
            d"lbl: print ${PCalRenderPass.describeExpr(expr)};\n".indented +
            d"} } *)\n" +
            d"\\* BEGIN TRANSLATION\n" +
            d"===="

        val (shouldSkip, expectedBehaviour) = try {
          (false, Right(TLAExprInterpreter.interpret(expr)(env = Map.empty)))
        } catch {
          case err@TLAExprInterpreter.Unsupported() =>
            (true, Left(err))
          case err@TLAExprInterpreter.TypeError() =>
            (false, Left(err))
        }
        whenever(!shouldSkip) {
          cases += 1
          expectedBehaviour match {
            case Left(_) => degenerateCases += 1
            case Right(_) =>
          }
          os.remove.all(outFile)
          os.write.over(testFile, data = mpcalSetup.linesIterator.map(line => s"$line\n"))

          def somethingBadHappened(): Unit = {
            os.makeDir.all(os.pwd / "fuzz_output")
            val testOut = os.temp.dir(dir = os.pwd / "fuzz_output", deleteOnExit = false)
            println(s"something bad happened. saving test to $testOut")
            os.copy.over(from = workDir, to = testOut)
          }

          try {
            val errs = PGo.run(Seq("gogen", "-s", testFile.toString(), "-o", outFile.toString()))
            assert(errs == Nil)
          } catch {
            case NonFatal(err) =>
              somethingBadHappened()
              throw err
          }

          os.proc("go", "mod", "download").call(cwd = workDir)

          try {
            val result = os.proc("go", "run", "./main").call(cwd = workDir, mergeErrIntoOut = true, timeout = 60000)
            val valueFromGo = TLAValue.parseFromString(result.out.text())
            expectedBehaviour match {
              case Left(err) =>
                fail(s"expected an error, because Scala-based interpreter threw one", err)
              case Right(valueFromScala) =>
                assert(valueFromGo == valueFromScala)
            }
          } catch {
            case err: os.SubprocessException =>
              expectedBehaviour match {
                case Left(_) =>
                  if (err.result.out.text().startsWith("panic: TLA+ type error")) {
                    // that's ok then
                  } else {
                    somethingBadHappened()
                    throw err
                  }
                case Right(_) =>
                  somethingBadHappened()
                  throw err
              }
            case NonFatal(err) =>
              somethingBadHappened()
              throw err
          }
        }
      }
    } finally {
      println(s"degenerate cases: $degenerateCases/$cases; ${degenerateCases.toDouble / cases.toDouble * 100}%")
    }
  }

  private def genFlatASTOptions(subExprs: List[TLAExpression])(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): List[Gen[TLAExpression]] = {
    sealed abstract class GenProvider {
      def genIterator: Iterator[Gen[TLAExpression]]
    }

    implicit class PartialFnGenProvider(iterable: Iterable[Gen[TLAExpression]]) extends GenProvider {
      override def genIterator: Iterator[Gen[TLAExpression]] = iterable.iterator
    }

    implicit class PartialFnIterableGenProvider(gen: Gen[TLAExpression]) extends GenProvider {
      override def genIterator: Iterator[Gen[TLAExpression]] = Iterator.single(gen)
    }

    val builtinModules = BuiltinModules.builtinModules.values.filter { mod =>
      (mod ne BuiltinModules.Reals) &&
        (mod ne BuiltinModules.Bags) &&
        (mod ne BuiltinModules.TLC) &&
        (mod ne BuiltinModules.Peano) &&
        (mod ne BuiltinModules.ProtoReals)
    }

    val cases: Iterator[PartialFunction[List[TLAExpression],GenProvider]] = Iterator(
      { case Nil => for {
          num <- Gen.posNum[Int]
        } yield TLANumber(TLANumber.IntValue(num), TLANumber.DecimalSyntax)
      },
      { case Nil => Gen.asciiPrintableStr.map(TLAString) }, // TODO: consider nonsense w/ unprintable ASCII
      { case Nil if env.exists(_.arity == 0) =>
        env.view
          .filter(_.arity == 0)
          .map { defn =>
            TLAGeneralIdentifier(defn.identifier.asInstanceOf[ScopeIdentifierName].name, Nil)
              .setRefersTo(defn)
          } : Iterable[Gen[TLAExpression]]
      },
      { case Nil =>
        builtinModules.view
          .flatMap(_.members)
          .filter(_.arity == 0)
          .map { defn =>
            TLAGeneralIdentifier(defn.identifier.asInstanceOf[ScopeIdentifierName].name, Nil)
              .setRefersTo(defn)
          } : Iterable[Gen[TLAExpression]]
      },
      { case List(expr: TLAExpression) =>
        for {
          ident <- Gen.identifier
        } yield TLADot(expr, TLAIdentifier(ident))
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty && env.exists(_.arity == subExprs.size) =>
        env.view.filter(_.arity == subExprs.size).map { defn =>
          Gen.const(TLAOperatorCall(defn.identifier, Nil, subExprs).setRefersTo(defn))
        }
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty =>
        builtinModules.view
          .flatMap(_.members)
          .filter(_.arity == subExprs.size)
          .map { defn =>
            TLAOperatorCall(defn.identifier, Nil, subExprs)
              .setRefersTo(defn)
          } : Iterable[Gen[TLAExpression]]
      },
      { case List(cond: TLAExpression, yes: TLAExpression, no: TLAExpression) =>
        Gen.const(TLAIf(cond, yes, no))
      },
      // LET exprs skipped on purpose; we need to understand scoping to get those right, so we leave it to other routines
      { case subExprs: List[TLAExpression] if subExprs.size >= 2 => // require at least one whole case arm's worth
        @tailrec
        def impl(subExprs: List[TLAExpression], armsAcc: List[TLACaseArm]): TLACase =
          subExprs match {
            case Nil => TLACase(armsAcc, None)
            case other :: Nil => TLACase(armsAcc, Some(other))
            case cond :: result :: restArms =>
              impl(restArms, TLACaseArm(cond, result) :: armsAcc)
          }

        Gen.const(impl(subExprs, Nil))
      },
      // skipping function defn for same reason as LET
      { case subExprs: List[TLAExpression] if subExprs.size >= 2 =>
        Gen.const(TLAFunctionCall(subExprs.head, subExprs.tail))
      },
      { case List(from: TLAExpression, to: TLAExpression) =>
        Gen.const(TLAFunctionSet(from, to))
      },
      // skipping function substitution; requires scoping
      { case Nil if anchorOpt.nonEmpty =>
        Gen.const(TLAFunctionSubstitutionAt()
          .setRefersTo(anchorOpt.get))
      },
      // skipping quantifiers, again due to scoping
      { case subExprs: List[TLAExpression] =>
        Gen.const(TLASetConstructor(subExprs))
      },
      // skipping set refinement, comprehension due to scoping
      { case subExprs: List[TLAExpression] =>
        Gen.const(TLATuple(subExprs))
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty =>
        for {
          idents <- Gen.listOfN(subExprs.size, Gen.identifier)
        } yield TLARecordConstructor((idents.view zip subExprs).map {
          case ident -> expr => TLARecordConstructorField(TLAIdentifier(ident), expr)
        }.toList)
      },
      { case subExprs: List[TLAExpression] if subExprs.nonEmpty =>
        for {
          idents <- Gen.listOfN(subExprs.size, Gen.identifier)
        } yield TLARecordSet((idents.view zip subExprs).map {
          case ident -> expr => TLARecordSetField(TLAIdentifier(ident), expr)
        }.toList)
      },
    )

    cases.flatMap { fn =>
      fn.unapply(subExprs)
        .map(_.genIterator)
    }
      .flatten
      .toList
  }

  def genNamedASTOptions(breadth: Int, makeExpr: (IdSet[DefinitionOne],Option[TLAFunctionSubstitutionPairAnchor])=>Gen[TLAExpression])(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): List[Gen[TLAExpression]] = {
    val options = mutable.ListBuffer[Gen[TLAExpression]]()

    def genQuantifierBound(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): Gen[TLAQuantifierBound] = for {
      tpe <- Gen.oneOf(TLAQuantifierBound.IdsType, TLAQuantifierBound.TupleType)
      ids <- tpe match {
        case TLAQuantifierBound.IdsType => Gen.identifier.map(id => List(TLAIdentifier(id).toDefiningIdentifier))
        case TLAQuantifierBound.TupleType => Gen.nonEmptyListOf(Gen.identifier.map(id => TLAIdentifier(id).toDefiningIdentifier))
      }
      set <- makeExpr(env, anchorOpt)
    } yield TLAQuantifierBound(tpe, ids, set)

    if(breadth >= 2) {
      def impl(count: Int, acc: List[TLAUnit])(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): Gen[TLAExpression] = {
        assert(count >= 1)
        if (count == 1) {
          makeExpr(env, anchorOpt).map { body =>
            TLALet(acc.reverse, body)
          }
        } else {
          for {
            name <- Gen.identifier.map(TLAIdentifier)
            // TODO: consider more complex argument shapes? this is just plain single names, for now
            idents <- Gen.listOf(Gen.identifier.map(name => TLAOpDecl(TLAOpDecl.NamedVariant(TLAIdentifier(name), 0))))
            body <- makeExpr(env ++ idents, anchorOpt)
            defn = TLAOperatorDefinition(ScopeIdentifierName(name), idents, body, isLocal = false)
            result <- impl(count - 1, defn :: acc)(env = env ++ defn.singleDefinitions, anchorOpt = anchorOpt)
          } yield result
        }
      }

      options += impl(breadth, Nil)

      options += (for {
        qbs <- Gen.listOfN(breadth - 1, genQuantifierBound)
        body <- makeExpr(env ++ qbs.view.flatMap(_.singleDefinitions), anchorOpt)
      } yield TLAFunction(qbs, body))
    }

    if(breadth >= 3) {
      // some of these might end up being quite "wide", but it's simpler than trying to accurately
      // count sub-expressions
      val genSubstitutionPair: Gen[TLAFunctionSubstitutionPair] = for {
        anchor <- Gen.delay(Gen.const(TLAFunctionSubstitutionPairAnchor()))
        keyCount <- Gen.chooseNum(1, (breadth - 1) / 2)
        keys <- Gen.listOfN(keyCount, for {
          indexCount <- Gen.chooseNum(1, math.max(((breadth - 1) / 2) / keyCount, 0))
          indices <- Gen.listOfN(indexCount, makeExpr(env, anchorOpt))
        } yield TLAFunctionSubstitutionKey(indices))
        value <- makeExpr(env, Some(anchor))
      } yield TLAFunctionSubstitutionPair(anchor, keys, value)

      options += (for {
        source <- makeExpr(env, anchorOpt)
        pairs <- Gen.listOfN((breadth - 1) / 2, genSubstitutionPair)
      } yield TLAFunctionSubstitution(source, pairs))
    }

    if(breadth >= 2) {
      options += (for {
        constructor <- Gen.oneOf(TLAQuantifiedExistential, TLAQuantifiedUniversal)
        bounds <- Gen.listOfN(breadth - 1, genQuantifierBound)
        body <- makeExpr(env ++ bounds.view.flatMap(_.singleDefinitions), anchorOpt)
      } yield constructor(bounds, body))
    }

    if(breadth == 2) {
      options += (for {
        binding <- genQuantifierBound
        when <- makeExpr(env ++ binding.singleDefinitions, anchorOpt)
      } yield TLASetRefinement(binding, when))
    }

    if(breadth >= 2) {
      options += (for {
        bounds <- Gen.listOfN(breadth - 1, genQuantifierBound)
        body <- makeExpr(env ++ bounds.view.flatMap(_.singleDefinitions), anchorOpt)
      } yield TLASetComprehension(body, bounds))
    }

    options.result()
  }

  private def forceOneOf[T](gens: List[Gen[T]]): Gen[T] = {
    require(gens.nonEmpty)
    if(gens.size == 1) {
      gens.head
    } else {
      Gen.choose(min = 0, max = gens.size - 1)
        .flatMap(gens)
    }
  }

  lazy val trueRandomExprGen: Gen[TLAExpression] = {
    def impl(size: Int)(implicit env: IdSet[DefinitionOne], anchorOpt: Option[TLAFunctionSubstitutionPairAnchor]): Gen[TLAExpression] =
      for {
        breadth <- Gen.oneOf(0 to size)
        expr <- locally {
          val namedOptions = genNamedASTOptions(breadth, impl(size / (breadth + 1))(_, _))
          val unnamedCase =
            for {
              subExprs <- Gen.listOfN(breadth, impl(size / (breadth + 1)))
              expr <- forceOneOf(genFlatASTOptions(subExprs))
            } yield expr

          if(namedOptions.nonEmpty) {
            Gen.oneOf(forceOneOf(namedOptions), unnamedCase)
          } else {
            unnamedCase // if there are no named options for this breadth, avoid choice-of-none error
          }
        }
      } yield expr

    Gen.sized(size => impl(size)(IdSet.empty, None))
  }

}
