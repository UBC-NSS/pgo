package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalMacroCall;

public class UnresolvableMacroCallIssue extends Issue {

	private final PlusCalMacroCall macroCall;

	public UnresolvableMacroCallIssue(PlusCalMacroCall macroCall) {
		this.macroCall = macroCall;
	}

	public PlusCalMacroCall getMacroCall() {
		return macroCall;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
