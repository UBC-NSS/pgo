package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/*
 * TLA AST PlusCalNode:
 * 
 * \E a, b, c : <expr>
 * or
 * \EE a, b, c : <expr>
 * 
 */
public class TLAExistential extends TLAExpression {
	
	private final List<TLAIdentifier> ids;
	private final TLAExpression body;

	public TLAExistential(SourceLocation location, List<TLAIdentifier> ids, TLAExpression body) {
		super(location);
		this.ids = ids;
		this.body = body;
	}
	
	@Override
	public TLAExistential copy() {
		return new TLAExistential(getLocation(), ids.stream().map(TLAIdentifier::copy).collect(Collectors.toList()), body.copy());
	}
	
	public List<TLAIdentifier> getIds(){
		return ids;
	}
	
	public TLAExpression getBody() {
		return body;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((ids == null) ? 0 : ids.hashCode());
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
		TLAExistential other = (TLAExistential) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (ids == null) {
			return other.ids == null;
		} else return ids.equals(other.ids);
	}

}
