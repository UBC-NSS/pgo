package pgo.util

import scala.collection.immutable.{Iterable, Set, SetOps}
import scala.collection.{IterableFactory, IterableFactoryDefaults, mutable}

class IdSet[V] private (underlying: Set[IdSet.Id[V]]) extends Iterable[V] with SetOps[V, IdSet, IdSet[V]] with IterableFactoryDefaults[V, IdSet] {
  import IdSet.Id

  override def incl(elem: V): IdSet[V] =
    new IdSet(underlying.incl(new Id(elem)))

  override def excl(elem: V): IdSet[V] =
    new IdSet(underlying.excl(new Id(elem)))

  override def contains(elem: V): Boolean =
    underlying.contains(new Id(elem))

  override def iterator: Iterator[V] =
    underlying.iterator.map(_.t)

  override def toString: String =
    s"IdSet(${iterator.mkString(",")})"

  override def iterableFactory: IterableFactory[IdSet] = IdSet
}

object IdSet extends IterableFactory[IdSet] {
  private class Id[T](val t: T) {
    override def equals(obj: Any): Boolean =
      obj match {
        case other: Id[_] => t.asInstanceOf[AnyRef] eq other.t.asInstanceOf[AnyRef]
        case _ => false
      }

    override def hashCode(): Int = System.identityHashCode(t)
  }

  override def from[A](source: IterableOnce[A]): IdSet[A] =
    new IdSet(Set.from(source.iterator.map(new Id(_))))

  override def empty[A]: IdSet[A] =
    new IdSet(Set.empty)

  override def newBuilder[A]: mutable.Builder[A, IdSet[A]] = new mutable.Builder[A, IdSet[A]] {
    private val underlying = Set.newBuilder[Id[A]]

    override def clear(): Unit = underlying.clear()

    override def result(): IdSet[A] = new IdSet(underlying.result())

    override def addOne(elem: A): this.type = {
      underlying.addOne(new Id(elem))
      this
    }
  }
}
