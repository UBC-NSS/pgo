package pgo.model.golang.type;

import pgo.model.golang.GoNode;
import pgo.model.golang.GoNodeVisitor;

import java.util.Objects;

public class GoStructTypeField extends GoNode {
	private final String name;
	private final GoType type;
	
	public GoStructTypeField(String name, GoType type) {
		this.name = name;
		this.type = type;
	}
	
	public String getName() {
		return name;
	}
	
	public GoType getType() {
		return type;
	}

	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoStructTypeField that = (GoStructTypeField) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(type, that.type);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, type);
	}
}
