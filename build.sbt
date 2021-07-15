name := "pgo"
scalaVersion := "2.13.5"
javacOptions ++= Seq("-source", "1.8")

Compile / javaSource := baseDirectory.value / "src"
Test / javaSource := baseDirectory.value / "test"
Compile / scalaSource := baseDirectory.value / "src"
Test / scalaSource := baseDirectory.value / "test"

libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value

libraryDependencies += "org.rogach" %% "scallop" % "4.0.2"
libraryDependencies += "io.spray" %%  "spray-json" % "1.3.6"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.2.0-M1"
libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.7.3"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test
libraryDependencies += "org.scalatestplus" %% "scalacheck-1-15" % "3.2.9.0" % Test
libraryDependencies += "io.github.java-diff-utils" % "java-diff-utils" % "4.9" % Test