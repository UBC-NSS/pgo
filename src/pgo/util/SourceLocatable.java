package pgo.util;

/**
 * 
 * A common abstract base, typically meant for AST nodes, that should be
 * implemented by anything that needs to be traced back to its
 * original location.
 * 
 * Implements the Origin interface so that any node of this type may be referenced
 * in a generic way.
 *
 */
public abstract class SourceLocatable implements Origin {
	
	public abstract SourceLocation getLocation();
	
	public <T, E extends Throwable> T accept(OriginVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
