package pgo.model.golang;

public class FunctionArgument extends Node {
	
	private String name;
	private Type type;

	public FunctionArgument(String name, Type type) {
		this.name = name;
		this.type = type;
	}

	public String getName() {
		return name;
	}

	public Type getType() {
		return type;
	}

}
