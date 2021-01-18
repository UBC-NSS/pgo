package pgo

import org.scalatest.funsuite.AnyFunSuite
import pgo.IntegrationTestingUtils.{testCompileFile, testRunGoCode}

import java.nio.file.{Path, Paths}
import scala.jdk.CollectionConverters._

class ExampleCodegenRunTest extends AnyFunSuite{
  def check(tag: String)(fileName: String, constants: Map[String,String], expectedOutput: String): Unit =
    test(tag) {
      testCompileFile(Paths.get("examples", fileName), constants.asJava, { compiledOutputPath =>
        testRunGoCode(compiledOutputPath, expectedOutput.linesIterator.toList.asJava)
      })
    }

  check("Euclid N=5")(
    fileName = "Euclid.tla",
    constants = Map("N" -> "5"),
    expectedOutput = "{24 1 have gcd 1}")

  check("counter procs=1 iters=1")(
    fileName = "counter.tla",
    constants = Map("procs" -> "1", "iters" -> "1"),
    expectedOutput = "1")

  check("counter procs=1 itera=64")(
    fileName = "counter.tla",
    constants = Map("procs" -> "1", "iters" -> "64"),
    expectedOutput = (1 to 64).mkString("\n"))

  check("counter procs=2 iters=1")(
    fileName = "counter.tla",
    constants = Map("procs" -> "2", "iters" -> "1"),
    expectedOutput =
      """1
        |2""".stripMargin)

  check("counter procs=64 iters=1")(
    fileName = "counter.tla",
    constants = Map("procs" -> "64", "iters" -> "1"),
    expectedOutput = (1 to 64).mkString("\n"))

  check("counter procs=32 iters=32")(
    fileName = "counter.tla",
    constants = Map("procs" -> "32", "iters" -> "32"),
    expectedOutput = (1 to 32*32).mkString("\n"))

  check("counter procs=64 iters=64")(
    fileName = "counter.tla",
    constants = Map("procs" -> "64", "iters" -> "64"),
    expectedOutput = (1 to 64*64).mkString("\n"))

  check("Queens N=1")(
    fileName = "Queens.tla",
    constants = Map("N" -> "1"),
    expectedOutput = "[[1]]")

  check("Queens N=2")(
    fileName = "Queens.tla",
    constants = Map("N" -> "2"),
    expectedOutput = "[]")

  check("Queens N=3")(
    fileName = "Queens.tla",
    constants = Map("N" -> "3"),
    expectedOutput = "[]")

  check("Queens N=4")(
    fileName = "Queens.tla",
    constants = Map("N" -> "4"),
    expectedOutput = "[[2 4 1 3] [3 1 4 2]]")

  check("Queens N=5")(
    fileName = "Queens.tla",
    constants = Map("N" -> "5"),
    expectedOutput = "[[1 3 5 2 4] [1 4 2 5 3] [2 4 1 3 5] [2 5 3 1 4] [3 1 4 2 5]" +
      " [3 5 2 4 1] [4 1 3 5 2] [4 2 5 3 1] [5 2 4 1 3] [5 3 1 4 2]]")

  check("Queens N=9")(
    fileName = "Queens.tla",
    constants = Map("N" -> "9"),
    expectedOutput = "[[1 3 6 8 2 4 9 7 5] [1 3 7 2 8 5 9 4 6] [1 3 8 6 9 2 5 7 4] [1 4 2 8 6 9 3 5 7] " +
      "[1 4 6 3 9 2 8 5 7] [1 4 6 8 2 5 3 9 7] [1 4 7 3 8 2 5 9 6] [1 4 7 9 2 5 8 6 3] " +
      "[1 4 8 3 9 7 5 2 6] [1 5 2 6 9 3 8 4 7] [1 5 7 2 6 3 9 4 8] [1 5 7 9 3 8 2 4 6] " +
      "[1 5 7 9 4 2 8 6 3] [1 5 9 2 6 8 3 7 4] [1 5 9 6 4 2 8 3 7] [1 6 2 9 7 4 8 3 5] " +
      "[1 6 4 2 7 9 3 5 8] [1 6 4 2 8 3 9 7 5] [1 6 8 3 7 4 2 9 5] [1 6 8 5 2 4 9 7 3] " +
      "[1 6 9 5 2 8 3 7 4] [1 7 4 6 9 2 5 3 8] [1 7 4 8 3 5 9 2 6] [1 7 4 8 3 9 6 2 5] " +
      "[1 7 5 8 2 9 3 6 4] [1 8 4 2 7 9 6 3 5] [1 8 5 3 6 9 2 4 7] [1 8 5 3 9 7 2 4 6] " +
      "[2 4 1 7 9 6 3 5 8] [2 4 7 1 3 9 6 8 5] [2 4 8 3 9 6 1 5 7] [2 4 9 7 3 1 6 8 5] " +
      "[2 4 9 7 5 3 1 6 8] [2 5 7 1 3 8 6 4 9] [2 5 7 4 1 3 9 6 8] [2 5 7 9 3 6 4 1 8] " +
      "[2 5 7 9 4 8 1 3 6] [2 5 8 1 3 6 9 7 4] [2 5 8 1 9 6 3 7 4] [2 5 8 6 9 3 1 4 7] " +
      "[2 5 8 6 9 3 1 7 4] [2 5 9 4 1 8 6 3 7] [2 6 1 3 7 9 4 8 5] [2 6 1 7 4 8 3 5 9] " +
      "[2 6 1 7 5 3 9 4 8] [2 6 1 9 5 8 4 7 3] [2 6 3 1 8 4 9 7 5] [2 6 9 3 5 8 4 1 7] " +
      "[2 7 5 1 9 4 6 8 3] [2 7 5 8 1 4 6 3 9] [2 7 9 6 3 1 4 8 5] [2 8 1 4 7 9 6 3 5] " +
      "[2 8 5 3 9 6 4 1 7] [2 8 6 9 3 1 4 7 5] [2 9 5 3 8 4 7 1 6] [2 9 6 3 5 8 1 4 7] " +
      "[2 9 6 3 7 4 1 8 5] [2 9 6 4 7 1 3 5 8] [3 1 4 7 9 2 5 8 6] [3 1 6 8 5 2 4 9 7] " +
      "[3 1 7 2 8 6 4 9 5] [3 1 7 5 8 2 4 6 9] [3 1 8 4 9 7 5 2 6] [3 1 9 7 5 2 8 6 4] " +
      "[3 5 2 8 1 4 7 9 6] [3 5 2 8 1 7 4 6 9] [3 5 7 1 4 2 8 6 9] [3 5 8 2 9 6 1 7 4] " +
      "[3 5 8 2 9 7 1 4 6] [3 5 9 2 4 7 1 8 6] [3 5 9 4 1 7 2 6 8] [3 6 2 7 1 4 8 5 9] " +
      "[3 6 2 9 5 1 8 4 7] [3 6 8 1 4 7 5 2 9] [3 6 8 1 5 9 2 4 7] [3 6 8 2 4 9 7 5 1] " +
      "[3 6 8 5 1 9 7 2 4] [3 6 8 5 2 9 7 4 1] [3 6 9 1 8 4 2 7 5] [3 6 9 2 5 7 4 1 8] " +
      "[3 6 9 2 8 1 4 7 5] [3 6 9 5 8 1 4 2 7] [3 6 9 7 1 4 2 5 8] [3 6 9 7 2 4 8 1 5] " +
      "[3 6 9 7 4 1 8 2 5] [3 7 2 4 8 1 5 9 6] [3 7 2 8 5 9 1 6 4] [3 7 2 8 6 4 1 5 9] " +
      "[3 7 4 2 9 5 1 8 6] [3 7 4 2 9 6 1 5 8] [3 7 4 8 5 9 1 6 2] [3 7 9 1 5 2 8 6 4] " +
      "[3 7 9 4 2 5 8 6 1] [3 8 2 4 9 7 5 1 6] [3 8 4 7 9 2 5 1 6] [3 8 6 1 9 2 5 7 4] " +
      "[3 8 6 4 9 1 5 7 2] [3 8 6 9 2 5 1 4 7] [3 9 2 5 8 1 7 4 6] [3 9 4 1 8 6 2 7 5] " +
      "[3 9 4 2 8 6 1 7 5] [3 9 4 8 5 2 6 1 7] [3 9 6 2 5 7 1 4 8] [3 9 6 4 1 7 5 2 8] " +
      "[3 9 6 8 2 4 1 7 5] [4 1 3 6 9 2 8 5 7] [4 1 5 2 9 7 3 8 6] [4 1 5 8 2 7 3 6 9] " +
      "[4 1 5 9 2 6 8 3 7] [4 1 7 9 2 6 8 3 5] [4 1 9 6 3 7 2 8 5] [4 2 5 8 1 3 6 9 7] " +
      "[4 2 7 3 1 8 5 9 6] [4 2 7 9 1 5 8 6 3] [4 2 7 9 1 8 5 3 6] [4 2 8 3 9 7 5 1 6] " +
      "[4 2 9 3 6 8 1 5 7] [4 2 9 5 1 8 6 3 7] [4 6 1 5 2 8 3 7 9] [4 6 1 9 5 8 2 7 3] " +
      "[4 6 1 9 7 3 8 2 5] [4 6 3 9 2 5 8 1 7] [4 6 3 9 2 8 5 7 1] [4 6 3 9 7 1 8 2 5] " +
      "[4 6 8 2 5 1 9 7 3] [4 6 8 2 5 7 9 1 3] [4 6 8 2 7 1 3 5 9] [4 6 8 3 1 7 5 2 9] " +
      "[4 6 9 3 1 8 2 5 7] [4 7 1 3 9 6 8 5 2] [4 7 1 6 9 2 8 5 3] [4 7 1 8 5 2 9 3 6] " +
      "[4 7 3 6 9 1 8 5 2] [4 7 3 8 2 5 9 6 1] [4 7 3 8 6 1 9 2 5] [4 7 3 8 6 2 9 5 1] " +
      "[4 7 5 2 9 1 3 8 6] [4 7 5 2 9 1 6 8 3] [4 7 5 2 9 6 8 3 1] [4 7 9 2 5 8 1 3 6] " +
      "[4 7 9 2 6 1 3 5 8] [4 7 9 6 3 1 8 5 2] [4 8 1 5 7 2 6 3 9] [4 8 5 3 1 6 2 9 7] " +
      "[4 8 5 3 1 7 2 6 9] [4 9 3 6 2 7 5 1 8] [4 9 5 3 1 6 8 2 7] [4 9 5 3 1 7 2 8 6] " +
      "[4 9 5 8 1 3 6 2 7] [5 1 6 4 2 8 3 9 7] [5 1 8 4 2 7 9 6 3] [5 1 8 6 3 7 2 4 9] " +
      "[5 2 4 1 7 9 3 6 8] [5 2 4 9 7 3 1 6 8] [5 2 6 1 3 7 9 4 8] [5 2 6 9 3 8 4 7 1] " +
      "[5 2 6 9 7 4 1 3 8] [5 2 8 1 4 7 9 6 3] [5 2 8 1 7 9 3 6 4] [5 2 8 3 7 4 1 9 6] " +
      "[5 2 8 3 7 9 1 6 4] [5 2 9 1 6 8 3 7 4] [5 2 9 6 3 7 4 1 8] [5 3 1 6 2 9 7 4 8] " +
      "[5 3 1 6 8 2 4 7 9] [5 3 1 7 2 8 6 4 9] [5 3 6 9 2 8 1 4 7] [5 3 6 9 7 1 4 2 8] " +
      "[5 3 6 9 7 2 4 8 1] [5 3 6 9 7 4 1 8 2] [5 3 8 4 2 9 6 1 7] [5 3 8 4 7 9 2 6 1] " +
      "[5 3 8 6 2 9 1 4 7] [5 3 8 6 2 9 7 1 4] [5 3 9 4 2 8 6 1 7] [5 3 9 6 8 2 4 1 7] " +
      "[5 7 1 4 2 8 6 9 3] [5 7 1 6 8 2 4 9 3] [5 7 2 4 8 1 3 9 6] [5 7 2 4 8 1 9 6 3] " +
      "[5 7 2 6 3 1 8 4 9] [5 7 2 6 8 1 4 9 3] [5 7 4 1 3 6 9 2 8] [5 7 4 1 3 8 6 2 9] " +
      "[5 7 4 1 3 9 6 8 2] [5 7 4 1 8 2 9 6 3] [5 7 9 3 8 2 4 6 1] [5 7 9 4 2 8 6 3 1] " +
      "[5 7 9 4 8 1 3 6 2] [5 8 1 4 7 3 6 9 2] [5 8 1 9 4 2 7 3 6] [5 8 2 7 3 1 9 4 6] " +
      "[5 8 2 7 3 6 9 1 4] [5 8 2 9 3 1 7 4 6] [5 8 2 9 6 3 1 4 7] [5 8 4 1 3 6 9 7 2] " +
      "[5 8 4 1 7 2 6 3 9] [5 8 4 9 7 3 1 6 2] [5 8 6 1 3 7 9 4 2] [5 8 6 9 3 1 7 4 2] " +
      "[5 9 2 4 7 3 8 6 1] [5 9 2 6 8 3 1 4 7] [5 9 4 6 8 2 7 1 3] [6 1 5 2 9 7 4 8 3] " +
      "[6 1 5 7 9 3 8 2 4] [6 1 5 7 9 4 2 8 3] [6 1 7 4 8 3 5 9 2] [6 2 5 7 9 3 8 4 1] " +
      "[6 2 5 7 9 4 8 1 3] [6 2 9 5 3 8 4 7 1] [6 3 1 4 7 9 2 5 8] [6 3 1 8 4 9 7 5 2] " +
      "[6 3 1 8 5 2 9 7 4] [6 3 5 8 1 4 2 7 9] [6 3 5 8 1 9 4 2 7] [6 3 5 8 1 9 7 2 4] " +
      "[6 3 7 2 4 8 1 5 9] [6 3 7 2 4 9 1 8 5] [6 3 7 2 8 5 1 4 9] [6 3 7 4 1 9 2 5 8] " +
      "[6 3 9 2 5 8 1 7 4] [6 3 9 4 1 8 2 5 7] [6 3 9 7 1 4 2 5 8] [6 4 1 7 9 2 8 5 3] " +
      "[6 4 2 7 9 3 5 8 1] [6 4 2 8 3 9 7 5 1] [6 4 2 8 5 3 1 9 7] [6 4 2 8 5 9 1 3 7] " +
      "[6 4 7 1 3 9 2 8 5] [6 4 7 1 8 2 5 3 9] [6 4 7 1 8 5 2 9 3] [6 4 9 1 3 7 2 8 5] " +
      "[6 4 9 1 5 2 8 3 7] [6 4 9 5 8 2 7 3 1] [6 8 1 5 9 2 4 7 3] [6 8 1 7 4 2 9 5 3] " +
      "[6 8 2 7 1 3 5 9 4] [6 8 3 1 9 2 5 7 4] [6 8 3 1 9 5 2 4 7] [6 8 3 7 9 2 5 1 4] " +
      "[6 8 5 2 9 7 4 1 3] [6 9 1 4 7 3 8 2 5] [6 9 3 1 8 4 2 7 5] [6 9 5 1 8 4 2 7 3] " +
      "[6 9 5 2 8 3 7 4 1] [6 9 5 8 1 3 7 2 4] [6 9 7 4 1 8 2 5 3] [7 1 4 2 8 6 9 3 5] " +
      "[7 1 4 6 9 3 5 8 2] [7 1 4 8 5 3 9 6 2] [7 1 6 2 5 8 4 9 3] [7 1 6 8 2 4 9 3 5] " +
      "[7 1 6 9 2 4 8 3 5] [7 1 8 5 2 9 3 6 4] [7 2 4 1 8 5 9 6 3] [7 2 4 6 1 9 5 3 8] " +
      "[7 2 4 9 1 8 5 3 6] [7 2 6 3 1 8 5 9 4] [7 2 8 6 1 3 5 9 4] [7 3 1 6 8 5 2 4 9] " +
      "[7 3 1 9 5 8 2 4 6] [7 3 6 2 5 1 9 4 8] [7 3 6 8 1 4 9 5 2] [7 3 6 8 1 5 9 2 4] " +
      "[7 3 8 2 4 6 9 5 1] [7 3 8 2 5 1 9 4 6] [7 3 8 6 2 9 5 1 4] [7 4 1 3 6 9 2 8 5] " +
      "[7 4 1 3 8 6 2 9 5] [7 4 1 3 9 6 8 5 2] [7 4 1 5 2 9 6 8 3] [7 4 1 8 2 9 6 3 5] " +
      "[7 4 1 8 5 3 6 9 2] [7 4 1 9 2 6 8 3 5] [7 4 2 5 8 1 3 6 9] [7 4 2 5 9 1 3 8 6] " +
      "[7 4 2 8 6 1 3 5 9] [7 4 2 9 5 1 8 6 3] [7 4 2 9 6 3 5 8 1] [7 4 8 1 5 9 2 6 3] " +
      "[7 4 8 3 9 6 2 5 1] [7 5 1 6 9 3 8 4 2] [7 5 1 8 6 3 9 2 4] [7 5 2 8 1 3 9 6 4] " +
      "[7 5 2 8 1 4 9 3 6] [7 5 3 9 6 8 2 4 1] [7 5 8 2 9 3 6 4 1] [7 5 8 2 9 6 3 1 4] " +
      "[7 9 1 3 5 8 2 4 6] [7 9 2 6 1 3 5 8 4] [7 9 3 5 2 8 6 4 1] [7 9 3 8 2 4 6 1 5] " +
      "[7 9 4 2 5 8 6 1 3] [7 9 6 3 1 8 5 2 4] [8 1 4 6 3 9 7 5 2] [8 1 4 7 3 6 9 2 5] " +
      "[8 1 4 7 5 2 9 6 3] [8 1 5 7 2 6 3 9 4] [8 2 4 1 7 9 6 3 5] [8 2 5 7 1 4 6 9 3] " +
      "[8 2 9 6 3 1 4 7 5] [8 3 1 4 7 9 6 2 5] [8 3 5 2 9 6 4 7 1] [8 3 5 9 1 6 4 2 7] " +
      "[8 4 1 7 5 2 6 9 3] [8 4 7 9 2 6 1 3 5] [8 4 9 1 5 2 6 3 7] [8 4 9 3 5 7 1 6 2] " +
      "[8 4 9 3 6 2 7 5 1] [8 4 9 7 3 1 6 2 5] [8 5 1 6 9 2 4 7 3] [8 5 2 4 1 7 9 3 6] " +
      "[8 5 2 4 1 7 9 6 3] [8 5 2 9 1 4 7 3 6] [8 5 2 9 7 4 1 3 6] [8 5 3 1 6 2 9 7 4] " +
      "[8 5 3 1 7 4 6 9 2] [8 5 3 6 9 7 1 4 2] [8 5 3 9 7 2 4 6 1] [8 6 1 3 5 7 9 4 2] " +
      "[8 6 1 3 7 9 4 2 5] [8 6 2 7 1 4 9 5 3] [8 6 3 9 7 1 4 2 5] [8 6 9 3 1 4 7 5 2] " +
      "[9 2 5 7 1 3 8 6 4] [9 2 5 7 4 1 8 6 3] [9 2 6 8 3 1 4 7 5] [9 3 5 2 8 1 7 4 6] " +
      "[9 3 6 2 7 1 4 8 5] [9 3 6 2 7 5 1 8 4] [9 3 6 4 1 8 5 7 2] [9 4 1 5 8 2 7 3 6] " +
      "[9 4 2 5 8 6 1 3 7] [9 4 2 7 3 6 8 1 5] [9 4 6 8 2 7 1 3 5] [9 4 6 8 3 1 7 5 2] " +
      "[9 4 8 1 3 6 2 7 5] [9 5 1 4 6 8 2 7 3] [9 5 1 8 4 2 7 3 6] [9 5 3 1 6 8 2 4 7] " +
      "[9 5 3 1 7 2 8 6 4] [9 5 3 8 4 7 1 6 2] [9 5 8 4 1 7 2 6 3] [9 6 2 7 1 3 5 8 4] " +
      "[9 6 3 1 8 5 2 4 7] [9 6 3 7 2 8 5 1 4] [9 6 4 2 8 5 7 1 3] [9 6 4 7 1 8 2 5 3] " +
      "[9 6 8 2 4 1 7 5 3] [9 7 2 4 1 8 5 3 6] [9 7 3 8 2 5 1 6 4] [9 7 4 2 8 6 1 3 5]]")
}
