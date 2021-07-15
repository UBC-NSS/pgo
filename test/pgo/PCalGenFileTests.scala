package pgo

import com.github.difflib.{DiffUtils, UnifiedDiffUtils}

import scala.jdk.CollectionConverters._

class PCalGenFileTests extends FileTestSuite {
  override val testFiles: List[os.Path] =
    os.list.stream(os.pwd / "test" / "files" / "general")
      .filter(_.last.endsWith(".tla"))
      .toList

  testFiles.foreach { testFile =>
    test(s"pcalgen ${testFile.relativeTo(os.pwd)}") {
      val tmpFile = os.temp(contents = testFile.toSource)
      val errors = PGo.run(Seq("pcalgen", "-s", tmpFile.toString()))
      checkErrors(errors, testFile)
      if(errors.isEmpty) {
        val expectedFile = testFile / os.up / s"${testFile.last}.expectpcal"
        val expectedLines = if(os.exists(expectedFile)) os.read.lines(expectedFile) else IndexedSeq.empty
        val actualLines = os.read.lines(tmpFile)

        val patch = DiffUtils.diff(expectedLines.asJava, actualLines.asJava)
        val diff = UnifiedDiffUtils.generateUnifiedDiff("expected", "actual", expectedLines.asJava, patch, 5)

        withClue(diff.asScala.mkString("\n")) {
          if(expectedLines != actualLines) {
            if(!sys.env.contains("TESTS_DO_NOT_WRITE")) {
              os.write.over(testFile / os.up / s"${testFile.last}.outpcal", data = tmpFile.toSource)
            }
            fail(s"expected PCal codegen did not match actual")
          }
        }
      }
    }
  }
}