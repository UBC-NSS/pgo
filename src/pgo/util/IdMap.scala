package pgo.util

import scala.collection.immutable.{Iterable, Map, MapOps}
import scala.collection.{MapFactory, MapFactoryDefaults, mutable}

class IdMap[K, +V] private (underlying: Map[IdMap.Id[K],V]) extends Iterable[(K, V)] with MapOps[K, V, IdMap, IdMap[K, V]] with MapFactoryDefaults[K, V, IdMap, Iterable] {
  import IdMap.Id

  override def removed(key: K): IdMap[K, V] =
    new IdMap(underlying.removed(new Id(key)))

  override def updated[V1 >: V](key: K, value: V1): IdMap[K, V1] =
    new IdMap(underlying.updated(new Id(key), value))

  override def get(key: K): Option[V] = underlying.get(new Id(key))

  override def iterator: Iterator[(K, V)] = underlying.iterator.map {
    case (idKey, value) => (idKey.t, value)
  }

  override def toString(): String =
    s"IdMap(${iterator.mkString(",")})"

  override def mapFactory: MapFactory[IdMap] = IdMap
}

object IdMap extends MapFactory[IdMap] {
  private class Id[T](val t: T) {
    override def equals(obj: Any): Boolean =
      obj match {
        case other: Id[_] => t.asInstanceOf[AnyRef] eq other.t.asInstanceOf[AnyRef]
        case _ => false
      }

    override def hashCode(): Int = System.identityHashCode(t)
  }

  override def empty[K, V]: IdMap[K, V] = new IdMap(Map.empty[Id[K],V])

  override def from[K, V](it: IterableOnce[(K, V)]): IdMap[K, V] =
    new IdMap(Map.from(it.iterator.map { case key -> value => new Id(key) -> value }))

  override def newBuilder[K, V]: mutable.Builder[(K, V), IdMap[K, V]] = new mutable.Builder[(K, V), IdMap[K, V]] {
    private val underlying = Map.newBuilder[Id[K], V]

    override def clear(): Unit = underlying.clear()

    override def result(): IdMap[K, V] = new IdMap(underlying.result())

    override def addOne(elem: (K, V)): this.type = {
      underlying.addOne((new Id(elem._1), elem._2))
      this
    }
  }
}
