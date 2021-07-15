package pgo.model

import pgo.util.Description
import Description._

import scala.annotation.tailrec
import scala.collection.View

sealed abstract class SourceLocation {
  override def toString: String = shortDescription.linesIterator.mkString("\n")
  def shortDescription: Description
  def longDescription: Description

  def maybeOffset: Int = -1

  def derivedVia(description: Description, viaPos: SourceLocation = SourceLocationInternal): SourceLocation =
    DerivedSourceLocation(this, viaPos, description)

  def ++(other: SourceLocation): SourceLocation = {
    (this, other) match {
      case (SourceLocationUnknown, SourceLocationUnknown) => SourceLocationUnknown
      case (SourceLocationInternal, SourceLocationInternal) => SourceLocationInternal
      case (SourceLocationWithUnderlying(underlying1, startOffset1, endOffset1, startLine1, endLine1, startColumn1, endColumn1), SourceLocationWithUnderlying(underlying2, startOffset2, endOffset2, startLine2, endLine2, startColumn2, endColumn2)) =>
        require(underlying1 eq underlying2, s"SourceLocation combination needs two source locations that share the same underlying text")
        SourceLocationWithUnderlying(
          underlying = underlying1,
          startOffset = startOffset1 min startOffset2,
          endOffset = endOffset1 max endOffset2,
          startLine = startLine1 min startLine2,
          endLine = endLine1 max endLine2,
          startColumn =
            if(startLine1 == startLine2) startColumn1 min startColumn2
            else if(startLine1 < startLine2) startColumn1
            else startColumn2,
          endColumn =
            if(endLine1 == endLine2) endColumn1 max endColumn2
            else if(endLine1 > endLine2) endColumn1
            else endColumn2)
      case (l, r) =>
        throw new IllegalArgumentException(s"requirement failed: SourceLocation combination must involve two locations of the same type: $l ++ $r")
    }
  }
}

object SourceLocation {
  def unknown: SourceLocation = SourceLocationUnknown
  def internal: SourceLocation = SourceLocationInternal

  def apply(underlyingText: UnderlyingText, startOffset: Int, endOffset: Int, startLine: Int, endLine: Int, startColumn: Int, endColumn: Int): SourceLocation =
    SourceLocationWithUnderlying(underlyingText, startOffset = startOffset, endOffset = endOffset,
      startLine = startLine, endLine = endLine, startColumn = startColumn, endColumn = endColumn)

  trait UnderlyingText {
    def name: String
    def getLines(startLine: Int, length: Int): List[String]
  }

  class UnderlyingFile(path: os.Path) extends UnderlyingText {
    override def name: String = path.toString
    override def getLines(startLine: Int, length: Int): List[String] = {
      val span = os.read.lines.stream(path)
        .slice(startLine, startLine + length)
      if(length > 3) {
        var first: String = null
        var last: String = null
        span.foreach {
          case line if first eq null => first = line
          case line => last = line
        }
        List(first, last)
      } else {
        span.toList
      }
    }
  }
  class UnderlyingString(str: String, override val name: String = "<string>") extends UnderlyingText {
    override def getLines(startLine: Int, length: Int): List[String] = {
      val span = str.linesIterator.slice(startLine, startLine + length)
      if(length > 3) {
        var first: String = null
        var last: String = null
        span.foreach {
          case line if first eq null => first = line
          case line => last = line
        }
        List(first, last)
      } else {
        span.toList
      }
    }
  }
}

case object SourceLocationUnknown extends SourceLocation {
  override val shortDescription: Description = d"<unknown>"
  override def longDescription: Description = shortDescription
}

case object SourceLocationInternal extends SourceLocation {
  override val shortDescription: Description = d"<internal>"
  override def longDescription: Description = shortDescription
}

final case class SourceLocationWithUnderlying(underlying: SourceLocation.UnderlyingText,
                                              startOffset: Int, endOffset: Int,
                                              startLine: Int, endLine: Int,
                                              startColumn: Int, endColumn: Int) extends SourceLocation
{
  require(startLine <= endLine && startOffset <= endOffset)

  override def maybeOffset: Int = startOffset

  override val shortDescription: Description =
    d"${underlying.name}:${startLine+1}.${startColumn+1}${
      if(startLine != endLine) d"--${endLine+1}.${endColumn+1}" else if(startColumn != endColumn) d"-${endColumn+1}" else d""
    }"

  override lazy val longDescription: Description = {
    d"$shortDescription\n${
      val length = endLine - (startLine - 1)
      val (lines, atEOF) = locally {
        val lines = underlying.getLines(startLine-1, length+1)
        assert(lines.nonEmpty)
        if(lines.size == length) {
          (if(lines.size == 1) List("") else lines.tail, true)
        } else {
          (lines.tail, false)
        }
      }
      val firstLine = lines.head
      if (length > 1) {
        val header = (View.fill(startColumn)(d" ") ++ View.fill(firstLine.length - startColumn)(d"v")).flattenDescriptions
        val footer = (View.fill(endColumn-1)(d"^") ++ (if(atEOF) View(d" EOF") else View.empty)).flattenDescriptions
        if (length > 3) {
          d"$header\n$firstLine\n...\n${lines.last}\n$footer"
        } else {
          d"$header\n${lines.view.map(_.toDescription.ensureLineBreakBefore).flattenDescriptions}\n$footer"
        }
      } else {
        val effectiveEndColumn = if(startColumn == endColumn) startColumn + 1 else endColumn
        val footer = (View.fill(startColumn)(d" ") ++ View.fill(effectiveEndColumn - startColumn)(d"^") ++ (if(atEOF) View(d" EOF") else View.empty)).flattenDescriptions
        d"$firstLine\n$footer"
      }
    }"
  }
}

final case class DerivedSourceLocation(underlying: SourceLocation, via: SourceLocation, method: Description) extends SourceLocation {
  override def maybeOffset: Int = underlying.maybeOffset

  override def shortDescription: Description = underlying.shortDescription

  override def longDescription: Description = d"${underlying.longDescription}\n${
    d"derived via $method at ${via.longDescription}".indented
  }"
}
