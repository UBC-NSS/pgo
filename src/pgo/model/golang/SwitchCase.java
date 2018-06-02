package pgo.model.golang;

import java.util.List;

public class SwitchCase extends Node {
	private Expression condition;
	private List<Statement> block;
	
	public SwitchCase(Expression condition, List<Statement> block) {
		super();
		this.condition = condition;
		this.block = block;
	}

	public Expression getCondition() {
		return condition;
	}

	public List<Statement> getBlock() {
		return block;
	}
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}