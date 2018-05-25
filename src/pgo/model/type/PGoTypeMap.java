package pgo.model.type;

import pgo.errors.IssueContext;

import java.util.Map;
import java.util.Set;

/**
 * Represents a map.
 */
public class PGoTypeMap extends PGoType {
	private PGoType keyType;
	private PGoType valueType;

	public PGoTypeMap(PGoType keyType, PGoType valueType) {
		this.keyType = keyType;
		this.valueType = valueType;
	}

	public PGoType getKeyType() {
		return keyType;
	}

	public PGoType getValueType() {
		return valueType;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeMap)) {
			return false;
		}
		PGoTypeMap other = (PGoTypeMap) p;
		return keyType.equals(other.keyType) && valueType.equals(other.valueType);
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		return keyType.contains(v) || valueType.contains(v);
	}

	@Override
	public boolean containsVariables() {
		return keyType.containsVariables() || valueType.containsVariables();
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		keyType.collectVariables(vars);
		valueType.collectVariables(vars);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		return new PGoTypeMap(keyType.substitute(mapping), valueType.substitute(mapping));
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		return new PGoTypeMap(keyType.realize(ctx), valueType.realize(ctx));
	}

	@Override
	public String toTypeName() {
		return "Map[" + keyType.toTypeName() + "]" + valueType.toTypeName();
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public String toGo() {
		return "datatypes.Map";
	}
}
