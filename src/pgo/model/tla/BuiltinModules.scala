package pgo.model.tla

import pgo.model.{Definition, DefinitionOne, SourceLocation}

import scala.collection.mutable

object BuiltinModules {
  abstract class TLABuiltinModule(id: String) extends DefinitionOne {
    override val identifier: Definition.ScopeIdentifierName =
      Definition.ScopeIdentifierName(TLAIdentifier(id).setSourceLocation(SourceLocation.internal))
    override def arity: Int = 0

    private[this] val membersAcc = mutable.ListBuffer[TLABuiltinOperator]()
    def members: List[TLABuiltinOperator] = membersAcc.result()

    protected final def extend(module: TLABuiltinModule): Unit =
      membersAcc ++= module.members

    protected final def op(op: TLABuiltinOperator): Unit =
      membersAcc += op

    protected final def symOp(sym: TLASymbol.Symbol): Unit =
      membersAcc += TLABuiltinOperator(
        module = this,
        identifier = Definition.ScopeIdentifierSymbol(TLASymbol(sym).setSourceLocation(SourceLocation.internal)),
        arity = if(sym.isPrefix || sym.isPostfix) 1 else 2)

    protected final def alphaOp(name: String, arity: Int): Unit =
      membersAcc += TLABuiltinOperator(
        module = this,
        identifier = Definition.ScopeIdentifierName(TLAIdentifier(name).setSourceLocation(SourceLocation.internal)),
        arity = arity)

    lazy val membersMap: Map[Definition.ScopeIdentifier,TLABuiltinOperator] =
      members.view.map(op => op.identifier -> op).toMap

    final def memberAlpha(name: String): TLABuiltinOperator =
      membersMap(Definition.ScopeIdentifierName(TLAIdentifier(name)))

    final def memberSym(sym: TLASymbol.Symbol): TLABuiltinOperator =
      membersMap(Definition.ScopeIdentifierSymbol(TLASymbol(sym)))
  }

  final case class TLABuiltinOperator(module: TLABuiltinModule, identifier: Definition.ScopeIdentifier, arity: Int) extends DefinitionOne

  // these operators are always available
  object Intrinsics extends TLABuiltinModule("") {
    // logic
    symOp(TLASymbol.LogicalAndSymbol)
    symOp(TLASymbol.LogicalOrSymbol)
    symOp(TLASymbol.LogicalNotSymbol)
    symOp(TLASymbol.ImpliesSymbol)
    symOp(TLASymbol.EquivSymbol)
    alphaOp("TRUE", 0)
    alphaOp("FALSE", 0)
    alphaOp("BOOLEAN", 0)

    // sets
    symOp(TLASymbol.EqualsSymbol)
    symOp(TLASymbol.NotEqualsSymbol)
    symOp(TLASymbol.InSymbol)
    symOp(TLASymbol.NotInSymbol)
    symOp(TLASymbol.IntersectSymbol)
    symOp(TLASymbol.UnionSymbol)
    symOp(TLASymbol.SubsetOrEqualSymbol)
    symOp(TLASymbol.BackslashSymbol)
    symOp(TLASymbol.PrefixSubsetSymbol)
    symOp(TLASymbol.PrefixUnionSymbol)

    // functions
    symOp(TLASymbol.DomainSymbol)

    // strings
    alphaOp("STRING", 0)

    // action
    symOp(TLASymbol.PrimeSymbol)
    symOp(TLASymbol.EnabledSymbol)
    symOp(TLASymbol.UnchangedSymbol)
    symOp(TLASymbol.CDotSymbol)

    // temporal
    symOp(TLASymbol.TLAlwaysSymbol)
    symOp(TLASymbol.TLEventuallySymbol)
    symOp(TLASymbol.SequencingSymbol)
    symOp(TLASymbol.PlusArrowSymbol)
  }

  lazy val builtinModules: Map[Definition.ScopeIdentifier,TLABuiltinModule] = Iterator(
    TLC,
    Sequences, FiniteSets, Bags,
    Peano, ProtoReals, Naturals, Integers, Reals,
  ).map(mod => mod.identifier -> mod).toMap

  object TLC extends TLABuiltinModule("TLC") {
    alphaOp("Print", 2)
    alphaOp("PrintT", 1)
    alphaOp("Assert", 2)
    alphaOp("JavaTime", 0)
    symOp(TLASymbol.ColonGreaterThanSymbol)
    symOp(TLASymbol.DoubleAtSignSymbol)
    alphaOp("Permutations", 1)
    alphaOp("SortSeq", 2)
  }

  object Sequences extends TLABuiltinModule("Sequences") {
    alphaOp("Seq", 1)
    alphaOp("Len", 1)
    symOp(TLASymbol.OSymbol)
    alphaOp("Append", 2)
    alphaOp("Head", 1)
    alphaOp("Tail", 1)
    alphaOp("SubSeq", 3)
    alphaOp("SelectSeq", 2)
  }

  object FiniteSets extends TLABuiltinModule("FiniteSets") {
    alphaOp("IsFiniteSet", 1)
    alphaOp("Cardinality", 1)
  }

  object Bags extends TLABuiltinModule("Bags") {
    alphaOp("IsABag", 1)
    alphaOp("BagToSet", 1)
    alphaOp("SetToBag", 1)
    alphaOp("BagIn", 2)
    alphaOp("EmptyBag", 0)
    alphaOp("CopiesIn", 2)
    symOp(TLASymbol.OPlusSymbol)
    symOp(TLASymbol.OMinusSymbol)
    alphaOp("BagUnion", 1)
    symOp(TLASymbol.SquareSupersetOrEqualSymbol)
    alphaOp("SubBag", 1)
    alphaOp("BagOfAll", 2)
    alphaOp("BagCardinality", 1)
  }

  object Peano extends TLABuiltinModule("Peano") {
    alphaOp("PeanoAxioms", 3)
    alphaOp("Succ", 0)
    alphaOp("Nat", 0)
    alphaOp("Zero", 0)
  }

  object ProtoReals extends TLABuiltinModule("ProtoReals") {
    extend(Peano)

    alphaOp("IsModelOfReals", 4)
    alphaOp("RM", 0)
    alphaOp("Real", 0)
    alphaOp("Infinity", 0)
    alphaOp("MinusInfinity", 0)
    symOp(TLASymbol.PlusSymbol)
    symOp(TLASymbol.AsteriskSymbol)
    symOp(TLASymbol.LessThanOrEqualSymbol)
    symOp(TLASymbol.MinusSymbol)
    symOp(TLASymbol.SlashSymbol)
    alphaOp("Int", 0)
    symOp(TLASymbol.SuperscriptSymbol)
  }

  object Naturals extends TLABuiltinModule("Naturals") {
    op(ProtoReals.memberAlpha("Nat"))
    op(ProtoReals.memberSym(TLASymbol.PlusSymbol))
    op(ProtoReals.memberSym(TLASymbol.MinusSymbol))
    op(ProtoReals.memberSym(TLASymbol.AsteriskSymbol))
    op(ProtoReals.memberSym(TLASymbol.SuperscriptSymbol))
    op(ProtoReals.memberSym(TLASymbol.LessThanOrEqualSymbol))
    symOp(TLASymbol.GreaterThanOrEqualSymbol)
    symOp(TLASymbol.LessThanSymbol)
    symOp(TLASymbol.GreaterThanSymbol)
    symOp(TLASymbol.DotDotSymbol)
    symOp(TLASymbol.DivSymbol)
    symOp(TLASymbol.PercentSymbol)
  }

  object Integers extends TLABuiltinModule("Integers") {
    extend(Naturals)

    op(ProtoReals.memberAlpha("Int"))
    symOp(TLASymbol.NegationSymbol)
  }

  object Reals extends TLABuiltinModule("Reals") {
    extend(Integers)

    op(ProtoReals.memberAlpha("Real"))
    op(ProtoReals.memberSym(TLASymbol.SlashSymbol))
    op(ProtoReals.memberAlpha("Infinity"))
  }
}
