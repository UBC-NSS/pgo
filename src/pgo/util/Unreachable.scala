package pgo.util

case class Unreachable() extends RuntimeException("this code should never be reached")

object Unreachable {
  def !!! : Nothing = throw Unreachable()
}
