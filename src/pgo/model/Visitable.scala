package pgo.model

trait Visitable {
  import Visitable._

  def productIterator: Iterator[Any]

  def visit(strategy: Strategy = TopDownFirstStrategy)(fn: PartialFunction[Visitable,Unit]): Unit =
    strategy.execute(this, fn)

  def reduce[C](empty: =>C, reducer: (C,C) => C)(fn: PartialFunction[(Visitable,Seq[C]),C]): Unit = {
    def reduceSubNode(node: Any): C =
      node match {
        case visitable: Visitable =>
          val subNodeResults = visitable.productIterator.map(reduceSubNode).toSeq
          fn.applyOrElse((visitable,subNodeResults), { (_: (Visitable,Seq[C])) =>
            subNodeResults.foldLeft(empty)(reducer)
          })
        case map: Map[_,_] => map.valuesIterator.map(reduceSubNode).foldLeft(empty)(reducer)
        case iterable: Iterable[_] => iterable.iterator.map(reduceSubNode).foldLeft(empty)(reducer)
        case product: Product => product.productIterator.map(reduceSubNode).foldLeft(empty)(reducer)
        case _ => empty
      }
    reduceSubNode(this)
  }
}

object Visitable {
  trait Strategy {
    def execute(visitable: Any, fn: PartialFunction[Visitable,Unit]): Unit
  }

  def visitSubNodes(visitable: Any, fn: Any => Unit): Unit =
    visitable match {
      case map: Map[_,_] => map.valuesIterator.foreach(fn)
      case iterable: Iterable[_] => iterable.foreach(fn)
      case product: Product => product.productIterator.foreach(fn)
      case _ =>
    }

  object TopDownFirstStrategy extends Strategy {
    override def execute(visitable: Any, fn: PartialFunction[Visitable,Unit]): Unit =
      visitable match {
        case visitable: Visitable =>
          fn.applyOrElse(visitable, { (visitable: Visitable) =>
            visitable.productIterator.foreach(this.execute(_, fn))
          })
        case otherwise =>
          visitSubNodes(otherwise, this.execute(_, fn))
      }
  }

  object BottomUpFirstStrategy extends Strategy {
    override def execute(visitable: Any, fn: PartialFunction[Visitable,Unit]): Unit =
      visitable match {
        case visitable: Visitable =>
          visitable.productIterator.foreach(this.execute(_, fn))
          fn.applyOrElse(visitable, (_: Visitable) => ())
        case otherwise =>
          visitSubNodes(otherwise, this.execute(_, fn))
      }
  }
}
