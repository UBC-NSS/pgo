package pgo.model

import scala.reflect.ClassTag

trait RefersTo[T <: RefersTo.HasReferences] extends Rewritable {
  private var refersTo_ : Option[T] = None
  def refersTo: T = refersTo_.get
  def setRefersTo(refersTo: T): this.type = {
    refersTo_ = Some(refersTo)
    this
  }
  def hasRefersTo: Boolean = refersTo_.nonEmpty

  override def decorateLike(succ: this.type): this.type =
    super.decorateLike(succ.setRefersTo(refersTo))
}

object RefersTo {
  def unapply[T](candidate: Any)(implicit tag: ClassTag[T]): Option[T] =
    candidate match {
      case refersTo: RefersTo[_] =>
        refersTo.refersTo match {
          case tag(refersTo) =>
            Some(refersTo)
          case _ => None
        }
      case _ => None
    }

  trait HasReferences
}
