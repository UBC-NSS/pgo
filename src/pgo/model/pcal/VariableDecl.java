package pgo.model.pcal;

import pgo.model.tla.PGoTLAExpression;
import pgo.util.SourceLocation;

public class VariableDecl extends Node {
	
	String name;
	boolean isSet;
	PGoTLAExpression value;
	
	public VariableDecl(SourceLocation location, String name, boolean isSet, PGoTLAExpression value) {
		super(location);
		this.name = name;
		this.isSet = isSet;
		this.value = value;
	}
	
	public String getName() {
		return name;
	}
	
	public boolean getIsSet() {
		return isSet;
	}
	
	public PGoTLAExpression getValue(){
		return value;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (isSet ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((value == null) ? 0 : value.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		VariableDecl other = (VariableDecl) obj;
		if (isSet != other.isSet)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}