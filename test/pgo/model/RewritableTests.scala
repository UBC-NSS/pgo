package pgo.model

import org.scalatest.funsuite.AnyFunSuite

// can't be fields of an object; it messes with constructor signature
sealed abstract class Node extends Rewritable
final case class Split(left: Node, right: Node) extends Node
final case class Def(i: Int) extends Node with RefersTo.HasReferences
final case class Ref() extends Node with RefersTo[Def]

class RewritableTests extends AnyFunSuite {
  private val d1 = Def(1)
  private val d2 = Def(2)
  private val ast1 = Split(d1, Ref().setRefersTo(d1))

  test("namedParts returns immediate sub-nodes") {
    assert(ast1.namedParts.toList == List(d1))
  }

  test("rewrite preserves cross-references") {
    val ast2 = ast1.rewrite(Rewritable.BottomUpOnceStrategy) {
      case `d1` => d2
    }

    assert(ast2.left eq d2)
    assert(ast2.right.asInstanceOf[Ref].refersTo eq d2)
  }

}
