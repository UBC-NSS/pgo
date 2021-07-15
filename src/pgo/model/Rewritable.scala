package pgo.model

import pgo.util.IdMap

import java.lang.reflect.Constructor
import scala.annotation.tailrec

trait Rewritable extends Visitable {
  import Rewritable._

  def productIterator: Iterator[Any]

  /**
   * Creates an iterator over all "named things" contained within this Rewritable.
   * Assumption: an instance of RefersTo.HasReferences that is directly accessible from this case class's fields
   * (i.e not contained within some other nested Rewritable) is part of this AST node, and may be referenced
   * by other subtrees.
   */
  def namedParts: Iterator[RefersTo.HasReferences] = {
    def gatherOtherwise(subject: Any): Iterator[RefersTo.HasReferences] =
      subject match {
        case subject: Rewritable if subject ne this => Iterator.empty
        case map: Map[_, _] => map.valuesIterator.flatMap(gather)
        case iterable: Iterable[_] => iterable.iterator.flatMap(gather)
        case product: Product => product.productIterator.flatMap(gather)
        case _ => Iterator.empty
      }

    def gather(subject: Any): Iterator[RefersTo.HasReferences] =
      subject match {
        case subject: RefersTo.HasReferences => Iterator(subject) ++ gatherOtherwise(subject)
        case otherwise => gatherOtherwise(otherwise)
      }

    gather(this)
  }

  def decorateLike(succ: this.type): this.type = succ

  def mapChildren(fn: Any => Any): this.type = {
    @tailrec
    def applyRenamings(self: Rewritable, rewrittenSelf: Rewritable, existingRenamings: IdMap[RefersTo.HasReferences,RefersTo.HasReferences]): Rewritable = {
      val newRenamings = (self.namedParts zip rewrittenSelf.namedParts).filter(p => (p._1 ne p._2) && !existingRenamings.contains(p._1)).to(IdMap)
      def applyAllRenamings: Rewritable = {
        val allRenamings = existingRenamings ++ newRenamings
        Visitable.BottomUpFirstStrategy.execute(rewrittenSelf, {
          case ref: RefersTo[RefersTo.HasReferences] @unchecked if allRenamings.contains(ref.refersTo) =>
            def findTarget(target: RefersTo.HasReferences): RefersTo.HasReferences =
              allRenamings.get(target) match {
                case Some(target) => target
                case None => target
              }

            ref.setRefersTo(findTarget(ref.refersTo))
        })

        rewrittenSelf
      }

      if(newRenamings.isEmpty) {
        applyAllRenamings
      } else {
        val withDups = rewrittenSelf.withChildren(rewrittenSelf.productIterator.map { elem =>
          Rewritable.BottomUpOnceStrategy.execute(elem, {
            case ref: RefersTo[_] if newRenamings.contains(ref.refersTo) => ref.shallowCopy()
            case other => other
          })
        })
        if(withDups ne rewrittenSelf) {
          applyRenamings(self, withDups, existingRenamings ++ newRenamings)
        } else {
          applyAllRenamings
        }
      }
    }

    val result = withChildren(productIterator.map(fn))
    if(this ne result) {
      applyRenamings(this, result, IdMap.empty).asInstanceOf[this.type]
    } else {
      this
    }
  }

  final def withChildren(children: Iterator[Any]): this.type = {
    val childrenSeq = children.toSeq
    if(childrenSeq.corresponds(productIterator)(_ forceEq _)) {
      this
    } else {
      decorateLike(constructLikeFromSeq(this, childrenSeq))
    }
  }

  final def shallowCopy(): this.type =
    decorateLike(constructLikeFromSeq(this, productIterator.toSeq))

  final def rewrite(strategy: Strategy = TopDownFirstStrategy)(fn: PartialFunction[Rewritable,Rewritable]): this.type =
    strategy.execute(this, fn).asInstanceOf[this.type]
}

object Rewritable {
  implicit class AnyOps(val lhs: Any) extends AnyVal {
    def forceEq(rhs: Any): Boolean =
      lhs.asInstanceOf[AnyRef] eq rhs.asInstanceOf[AnyRef]
  }

  trait Strategy {
    def execute(rewritable: Any, fn: PartialFunction[Rewritable,Rewritable]): Any
  }

  private val primitiveMap: Map[Class[_],Class[_]] = Map(
    Integer.TYPE -> classOf[Integer],
    java.lang.Byte.TYPE -> classOf[java.lang.Byte],
    Character.TYPE -> classOf[Character],
    java.lang.Boolean.TYPE -> classOf[java.lang.Boolean],
    java.lang.Double.TYPE -> classOf[java.lang.Double],
    java.lang.Float.TYPE -> classOf[java.lang.Float],
    java.lang.Long.TYPE -> classOf[java.lang.Float],
    java.lang.Short.TYPE -> classOf[java.lang.Short],
  )

  def constructLikeFromSeq[T](template: T, args: Seq[Any]): T = {
    val klass = template.getClass
    val constructor = klass.getConstructors()(0).asInstanceOf[Constructor[T]]
    val paramTypes = constructor.getParameterTypes
    require(paramTypes.length == args.size)
    (paramTypes.view zip args.view).zipWithIndex.foreach {
      case ((paramType, arg), idx) =>
        val effectiveParamType =
          if(paramType.isPrimitive) {
            primitiveMap(paramType)
          } else paramType
        require(effectiveParamType.isAssignableFrom(arg.getClass), s"type mismatch for argument $idx when constructing $klass")
    }
    constructor.newInstance(args:_*)
  }

  def transformSubNodes(rewritable: Any, fn: Any => Any): Any =
    rewritable match {
      case map: Map[_,_] =>
        val result = map.view.mapValues(fn).to(map.mapFactory)
        if(map.keysIterator.forall(k => map(k) forceEq result(k))) map
        else result
      case iterable: Iterable[_] =>
        val result = iterable.map(fn)
        if(result.corresponds(iterable)(_ forceEq _)) iterable
        else result
      case product: Product =>
        val resultArgs = product.productIterator.map(fn).toSeq
        if(product.productIterator.corresponds(resultArgs)(_ forceEq _)) product
        else constructLikeFromSeq(product, resultArgs)
      case any => any
    }

  object TopDownFirstStrategy extends Strategy {
    override def execute(rewritable: Any, fn: PartialFunction[Rewritable,Rewritable]): Any =
      rewritable match {
        case rewritable: Rewritable =>
          val result = fn.applyOrElse[Rewritable,Rewritable](rewritable, identity)
          if(result eq rewritable) {
            rewritable.mapChildren(this.execute(_, fn))
          } else {
            result
          }
        case otherwise =>
          transformSubNodes(otherwise, this.execute(_, fn))
      }
  }

  object BottomUpOnceStrategy extends Strategy {
    override def execute(rewritable: Any, fn: PartialFunction[Rewritable,Rewritable]): Any =
      rewritable match {
        case rewritable: Rewritable =>
          fn.applyOrElse(rewritable.mapChildren(this.execute(_, fn)), identity[Rewritable])
        case otherwise =>
          transformSubNodes(otherwise, this.execute(_, fn))
      }
  }
}
