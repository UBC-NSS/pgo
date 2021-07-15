package pgo

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.util.Description
import pgo.model.SourceLocation
import pgo.parser.{PCalParser, TLAParser}
import Description._
import pgo.trans.PCalRenderPass

class PCalReadWriteTests extends AnyFunSuite {
  def check(path: os.Path)(implicit pos: Position): Unit = {
    test(path.relativeTo(os.pwd).toString()) {
      val underlying = new SourceLocation.UnderlyingFile(path)
      val fileContents = os.read(path)
      withClue(s"original file:\n$fileContents") {
        val tlaModule = TLAParser.readModuleBeforeTranslation(
          underlying = underlying, seq = fileContents)
        val pcalAlgorithm = PCalParser.readAlgorithm(
          underlying = underlying, contents = fileContents, tlaModule = tlaModule)

        val renderedContentsLines = d"(*\n${PCalRenderPass(pcalAlgorithm)}\n*)"
          .linesIterator.toBuffer
        val renderedContents = renderedContentsLines.mkString("\n")

        withClue(d"rendered file:\n$renderedContents") {
          val reparsedAlgorithm = PCalParser.readAlgorithm(
            new SourceLocation.UnderlyingString(renderedContents), renderedContents, tlaModule)

          assert(pcalAlgorithm == reparsedAlgorithm)
        }
      }
    }
  }

  check(os.pwd / "examples" / "Queens.tla")
  check(os.pwd / "examples" / "Euclid.tla")
  check(os.pwd / "examples" / "pgo2pc.tla")
  check(os.pwd / "examples" / "2pc.tla")
  check(os.pwd / "examples" / "round_robin.tla")
  check(os.pwd / "examples" / "counter.tla")
  check(os.pwd / "examples" / "DijkstraMutex.tla")
}
