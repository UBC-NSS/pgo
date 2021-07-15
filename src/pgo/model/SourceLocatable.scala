package pgo.model

trait SourceLocatable {
  private var _sourceLocation: SourceLocation = SourceLocation.unknown

  def sourceLocation: SourceLocation = _sourceLocation

  def setSourceLocation(sourceLocation: SourceLocation): this.type = {
    _sourceLocation = sourceLocation
    this
  }
}
