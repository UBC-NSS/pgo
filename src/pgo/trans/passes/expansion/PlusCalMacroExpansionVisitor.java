package pgo.trans.passes.expansion;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.stream.Collectors;

public class PlusCalMacroExpansionVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final IssueContext ctx;
	private final Map<String, PlusCalMacro> macros;
	private final Set<String> recursionSet;
	private final Map<String, TLAExpression> macroArgs;
	private final TLAExpressionMacroSubstitutionVisitor macroSubst;

	public PlusCalMacroExpansionVisitor(IssueContext ctx, Map<String, PlusCalMacro> macros, Set<String> recursionSet, Map<String, TLAExpression> macroArgs) {
		this.ctx = ctx;
		this.macros = macros;
		this.recursionSet = recursionSet;
		this.macroArgs = macroArgs;
		this.macroSubst = new TLAExpressionMacroSubstitutionVisitor(ctx, macroArgs);
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> stmts) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement stmt : stmts) {
			result.addAll(stmt.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		return Collections.singletonList(new PlusCalLabeledStatements(plusCalLabeledStatements.getLocation(),
				plusCalLabeledStatements.getLabel(), substituteStatements(plusCalLabeledStatements.getStatements())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		return Collections.singletonList(new PlusCalWhile(
				plusCalWhile.getLocation(), plusCalWhile.getCondition().accept(macroSubst), substituteStatements(plusCalWhile.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		return Collections.singletonList(new PlusCalIf(
				plusCalIf.getLocation(), plusCalIf.getCondition().accept(macroSubst), substituteStatements(plusCalIf.getYes()), substituteStatements(plusCalIf.getNo())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		return Collections.singletonList(new PlusCalEither(
				plusCalEither.getLocation(), plusCalEither.getCases().stream().map(this::substituteStatements).collect(Collectors.toList())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<PlusCalAssignmentPair> pairs = new ArrayList<>();
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			pairs.add(new PlusCalAssignmentPair(
					pair.getLocation(),
					pair.getLhs().accept(macroSubst),
					pair.getRhs().accept(macroSubst)));
		}
		return Collections.singletonList(new PlusCalAssignment(
				plusCalAssignment.getLocation(), pairs));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return Collections.singletonList(new PlusCalReturn(plusCalReturn.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		return Collections.singletonList(new PlusCalSkip(plusCalSkip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		return Collections.singletonList(new PlusCalCall(
				plusCalCall.getLocation(), plusCalCall.getTarget(), plusCalCall.getArguments().stream().map(a -> a.accept(macroSubst)).collect(Collectors.toList())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		if (recursionSet.contains(macroCall.getTarget())) {
			ctx.error(new RecursiveMacroCallIssue(macroCall));
		} else if (macros.containsKey(macroCall.getTarget())) {
			PlusCalMacro macro = macros.get(macroCall.getTarget());
			if (macro.getParamIds().size() != macroCall.getArguments().size()) {
				ctx.error(new MacroArgumentCountMismatchIssue(macroCall, macro));
			} else {
				Map<String, TLAExpression> argsMap = new HashMap<>();
				for (int i = 0; i < macroCall.getArguments().size(); ++i) {
					argsMap.put(macro.getParamIds().get(i), macroCall.getArguments().get(i));
				}
				Set<String> innerRecursionSet = new HashSet<>(recursionSet);
				innerRecursionSet.add(macro.getName());

				PlusCalMacroExpansionVisitor innerVisitor = new PlusCalMacroExpansionVisitor(ctx.withContext(new ExpandingMacroCall(macroCall)), macros, innerRecursionSet, argsMap);
				List<PlusCalStatement> statements = new ArrayList<>();
				for (PlusCalStatement stmt : macro.getBody()) {
					statements.addAll(stmt.accept(innerVisitor));
				}
				return statements;
			}
		} else {
			ctx.error(new UnresolvableMacroCallIssue(macroCall));
		}
		return Collections.singletonList(new PlusCalSkip(macroCall.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
		// FIXME: ugly mutation-based hack to correctly handle nested renames
		Map<String,TLAExpression> recovery = new HashMap<>();
		List<PlusCalStatement> result = Collections.singletonList(new PlusCalWith(
				plusCalWith.getLocation(),
				plusCalWith.getVariables().stream().map(v -> {
					if (macroArgs.containsKey(v.getName())) {
						// TODO: error reporting in this case?
					}
					PlusCalVariableDeclaration replacement = new PlusCalVariableDeclaration(v.getLocation(), v.getName(),
							v.isRef(), v.isSet(), v.getValue().accept(macroSubst));
					TLAGeneralIdentifier replacementID = new TLAGeneralIdentifier(SourceLocation.unknown(), v.getName(), Collections.emptyList());
					replacementID.setRefersTo(replacement);
					recovery.put(v.getName().getId(), macroArgs.put(v.getName().getId(), replacementID));
					return replacement;
				}).collect(Collectors.toList()),
				substituteStatements(plusCalWith.getBody())));
		for(String recName: recovery.keySet()) {
			if(recovery.get(recName) == null) {
				macroArgs.remove(recName);
			} else {
				macroArgs.put(recName, recovery.get(recName));
			}
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return Collections.singletonList(new PlusCalPrint(plusCalPrint.getLocation(), plusCalPrint.getValue().accept(macroSubst)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssert(plusCalAssert.getLocation(), plusCalAssert.getCondition().accept(macroSubst)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return Collections.singletonList(new PlusCalAwait(plusCalAwait.getLocation(), plusCalAwait.getCondition().accept(macroSubst)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return Collections.singletonList(new PlusCalGoto(plusCalGoto.getLocation(), plusCalGoto.getTarget()));
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}
