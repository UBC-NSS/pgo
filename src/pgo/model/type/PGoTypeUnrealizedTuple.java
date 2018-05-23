package pgo.model.type;

import java.util.*;

import pgo.errors.IssueContext;

/**
 * Represents an unrealized tuple.
 */
public class PGoTypeUnrealizedTuple extends PGoType {
	private Map<Integer, PGoType> elementTypes;
	private boolean sizeKnown;
	public enum RealType {
		Unknown, Chan, Set, Slice, Tuple
	}
	private RealType realType;

	public PGoTypeUnrealizedTuple() {
		this(new HashMap<>());
	}

	public PGoTypeUnrealizedTuple(Map<Integer, PGoType> elementTypes) {
		this(elementTypes, false);
	}

	public PGoTypeUnrealizedTuple(Map<Integer, PGoType> elementTypes, boolean sizeKnown) {
		this.elementTypes = new HashMap<>(elementTypes);
		this.sizeKnown = sizeKnown;
		this.realType = RealType.Unknown;
	}

	public Map<Integer, PGoType> getElementTypes() {
		return Collections.unmodifiableMap(elementTypes);
	}

	public boolean isSizeKnown() {
		return sizeKnown;
	}

	public RealType getRealType() {
		return realType;
	}

	public boolean isSimpleContainerType() {
		return realType == RealType.Chan || realType == RealType.Set || realType == RealType.Slice;
	}

	private int getProbableSize() {
		return elementTypes.keySet().stream().max(Comparator.naturalOrder()).orElse(-1) + 1;
	}

	public void harmonize(IssueContext ctx, PGoTypeSolver solver, PGoSimpleContainerType other) {
		PGoType elemType = other.getElementType();
		elementTypes.forEach((k, v) -> solver.addConstraint(ctx, new PGoTypeConstraint(this, elemType, v)));
		if (ctx.hasErrors()) {
			return;
		}
		// from this point onward, type unification was successful
		sizeKnown = true;
		if (other instanceof PGoTypeChan) {
			realType = RealType.Chan;
		} else if (other instanceof PGoTypeSet) {
			realType = RealType.Set;
		} else if (other instanceof PGoTypeSlice) {
			realType = RealType.Slice;
		} else {
			ctx.error(new UnrealizableTypeIssue(this));
			return;
		}
		elementTypes.clear();
		elementTypes.put(0, elemType);
	}

	public void harmonize(IssueContext ctx, PGoTypeConstraint constraint, PGoTypeSolver solver, PGoTypeTuple other) {
		List<PGoType> elemTypes = other.getElementTypes();
		int probableSize = getProbableSize();
		if (probableSize > elemTypes.size() || (sizeKnown && probableSize < elemTypes.size())) {
			ctx.error(new UnsatisfiableConstraintIssue(constraint, this, other));
			return;
		}
		elementTypes.forEach((k, v) -> solver.addConstraint(ctx, new PGoTypeConstraint(this, elemTypes.get(k), v)));
		if (ctx.hasErrors()) {
			return;
		}
		// from this point onward, type unification was successful
		sizeKnown = true;
		realType = RealType.Tuple;
		for (int i = 0; i < elemTypes.size(); i++) {
			if (elementTypes.containsKey(i)) {
				solver.addConstraint(ctx, new PGoTypeConstraint(this, elementTypes.get(i), elemTypes.get(i)));
			} else {
				elementTypes.put(i, elemTypes.get(i));
			}
		}
	}

	public void harmonize(IssueContext ctx, PGoTypeConstraint constraint, PGoTypeSolver solver, PGoTypeUnrealizedTuple other) {
		if (sizeKnown && other.sizeKnown && getProbableSize() != other.getProbableSize()) {
			ctx.error(new UnsatisfiableConstraintIssue(constraint, this, other));
			return;
		}
		if (realType != RealType.Unknown && other.realType != RealType.Unknown && realType != other.realType) {
			ctx.error(new UnsatisfiableConstraintIssue(constraint, this, other));
			return;
		}
		boolean isSizeKnown = sizeKnown || other.sizeKnown;
		int probableSize = Integer.max(getProbableSize(), other.getProbableSize());
		for (int i = 0; i < probableSize; i++) {
			if (elementTypes.containsKey(i) && other.elementTypes.containsKey(i)) {
				solver.addConstraint(ctx, new PGoTypeConstraint(this, elementTypes.get(i), other.elementTypes.get(i)));
			}
		}
		if (ctx.hasErrors()) {
			return;
		}
		// from this point onward, type unification was successful
		sizeKnown = isSizeKnown;
		other.sizeKnown = isSizeKnown;
		if (realType == RealType.Unknown) {
			realType = other.realType;
		}
		if (other.realType == RealType.Unknown) {
			other.realType = realType;
		}
		if (isSimpleContainerType()) {
			List<PGoType> ts = new ArrayList<>(elementTypes.values());
			ts.addAll(other.elementTypes.values());
			// collect constraints if ts.size() > 1
			if (ts.size() > 1) {
				PGoType first = ts.get(0);
				for (PGoType t : ts) {
					solver.addConstraint(ctx, new PGoTypeConstraint(this, first, t));
				}
			}
			// constraint types of the unrealized tuples
			if (ts.size() > 0) {
				HashMap<Integer, PGoType> m = new HashMap<>(Collections.singletonMap(0, ts.get(0)));
				elementTypes = m;
				other.elementTypes = m;
			}
			return;
		}
		HashMap<Integer, PGoType> m = new HashMap<>();
		for (int i = 0; i < probableSize; i++) {
			if (elementTypes.containsKey(i) && other.elementTypes.containsKey(i)) {
				solver.addConstraint(ctx, new PGoTypeConstraint(this, elementTypes.get(i), other.elementTypes.get(i)));
			}
			if (elementTypes.containsKey(i)) {
				m.put(i, elementTypes.get(i));
			} else if (other.elementTypes.containsKey(i)) {
				m.put(i, other.elementTypes.get(i));
			}
		}
		elementTypes = m;
		other.elementTypes = m;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof PGoTypeUnrealizedTuple)) {
			return false;
		}
		PGoTypeUnrealizedTuple other = (PGoTypeUnrealizedTuple) obj;
		return sizeKnown == other.sizeKnown && elementTypes.equals(other.elementTypes);
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		return elementTypes.values().stream().anyMatch(t -> t.contains(v));
	}

	@Override
	public boolean containsVariables() {
		return !sizeKnown || elementTypes.values().stream().anyMatch(PGoType::containsVariables);
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		elementTypes.values().forEach(t -> t.collectVariables(vars));
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		for (int i : elementTypes.keySet()) {
			elementTypes.put(i, elementTypes.get(i).substitute((mapping)));
		}
		return this;
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		if (!sizeKnown || realType == RealType.Unknown ||
				(getProbableSize() != 1 && realType != RealType.Tuple)) {
			ctx.error(new UnrealizableTypeIssue(this));
			return this;
		}
		if (realType == RealType.Tuple) {
			List<PGoType> sub = new ArrayList<>();
			for (int i = 0; i < getProbableSize(); i++) {
				if (!elementTypes.containsKey(i)) {
					ctx.error(new UnrealizableTypeIssue(this));
					return this;
				}
				sub.add(elementTypes.get(i).realize(ctx));
			}
			return new PGoTypeTuple(sub);
		}
		PGoType elemType = elementTypes.get(0);
		switch (realType) {
			case Chan:
				return new PGoTypeChan(elemType);
			case Set:
				return new PGoTypeSet(elemType);
			case Slice:
				return new PGoTypeSlice(elemType);
			case Tuple:
			case Unknown:
			default:
				throw new RuntimeException("Impossible");
		}
	}

	@Override
	public String toTypeName() {
		StringBuilder s = new StringBuilder();
		s.append("UnrealizedTuple");
		switch (realType) {
			case Chan:
				s.append("<").append("Chan").append(">");
				break;
			case Set:
				s.append("<").append("Set").append(">");
				break;
			case Slice:
				s.append("<").append("Slice").append(">");
				break;
			case Tuple:
				s.append("<").append("Tuple").append(">");
				break;
			case Unknown:
			default:
				// nothing
		}
		s.append("[");
		int probableSize = getProbableSize();
		for (int i = 0; i < probableSize; i++) {
			if (elementTypes.containsKey(i)) {
				s.append(elementTypes.get(i).toTypeName());
			} else {
				s.append("?");
			}
			if (i != probableSize - 1) {
				s.append(", ");
			}
		}
		if (!sizeKnown && probableSize > 0) {
			s.append(", ...?");
		}
		if (!sizeKnown && probableSize == 0) {
			s.append("...?");
		}
		s.append("]");
		return s.toString();
	}

	@Override
	public String toGo() {
		throw new IllegalStateException("Trying to convert an unrealized tuple to Go");
	}
}
