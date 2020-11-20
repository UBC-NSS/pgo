package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.atomicity.PlusCalStatementAtomicityInferenceVisitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;

public class PlusCalStatementCodeGenVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	private DefinitionRegistry registry;
	private Map<UID, Type> typeMap;
	private LocalVariableStrategy localStrategy;
	private GlobalVariableStrategy globalStrategy;
	private UID processUID;
	private GoBlockBuilder builder;
	private CriticalSectionTracker criticalSectionTracker;
	private Function<GoBlockBuilder, GoLabelName> awaitAction;

	private PlusCalStatementCodeGenVisitor(DefinitionRegistry registry, Map<UID, Type> typeMap, LocalVariableStrategy localStrategy,
	                                       GlobalVariableStrategy globalStrategy, UID processUID, GoBlockBuilder builder,
	                                       CriticalSectionTracker criticalSectionTracker,
	                                       Function<GoBlockBuilder, GoLabelName> awaitAction) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.localStrategy = localStrategy;
		this.globalStrategy = globalStrategy;
		this.processUID = processUID;
		this.builder = builder;
		this.criticalSectionTracker = criticalSectionTracker;
		this.awaitAction = awaitAction;
	}

	public PlusCalStatementCodeGenVisitor(DefinitionRegistry registry, Map<UID, Type> typeMap, LocalVariableStrategy localStrategy,
	                                      GlobalVariableStrategy globalStrategy, UID processUID, GoBlockBuilder builder) {
		this(registry, typeMap, localStrategy, globalStrategy, processUID, builder,
				new CriticalSectionTracker(registry, processUID, globalStrategy), ignored -> null);
	}

    private static void trackLocalVariableWrites(DefinitionRegistry registry, Set<UID> tracker, TLAExpression expression) {
        if (expression instanceof TLAGeneralIdentifier) {
            UID definitionUID = registry.followReference(expression.getUID());
            if (registry.isLocalVariable(definitionUID)) {
                tracker.add(definitionUID);
            }
        }
    }

	@Override
	public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		PlusCalLabel label = plusCalLabeledStatements.getLabel();
		builder.addComment(label.getName() + ":");

		criticalSectionTracker.start(builder, label.getUID(), new GoLabelName(label.getName()));
		for (PlusCalStatement stmt : plusCalLabeledStatements.getStatements()) {
			stmt.accept(this);
		}
		criticalSectionTracker.end(builder);
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		// note: here we don't directly compile the loop condition into the GoRoutineStatement loop condition due to
		// difficulties with intermediate variables and critical sections (if the condition is false
		// we may have to end the critical section after checking the condition)
		CriticalSectionTracker loopConditionCriticalSectionTracker = criticalSectionTracker.copy();
		Consumer<GoBlockBuilder> actionAtLoopEnd = criticalSectionTracker.actionAtLoopEnd();
		boolean loopBodyHasLabel = plusCalWhile.accept(new PlusCalStatementContainsLabelVisitor());
		try (GoBlockBuilder fb = builder.forLoop(null)) {
			try(GoIfBuilder loopCondition = fb.ifStmt(CodeGenUtil.invertCondition(
					fb, registry, typeMap, localStrategy, globalStrategy, plusCalWhile.getCondition()))) {
				try (GoBlockBuilder loopConditionBody = loopCondition.whenTrue()) {
					// if there are labels inside the loop, ensure that we end the critical section
					// when the loop condition fails as there must be a new label after the loop
					// if there are no labels inside the loop however, the critical section from before continues
					// uninterrupted
					if (loopBodyHasLabel) {
						loopConditionCriticalSectionTracker.end(loopConditionBody);
					}
					loopConditionBody.addStatement(new GoBreak());
				}
			}
			for (PlusCalStatement statement : plusCalWhile.getBody()) {
				statement.accept(new PlusCalStatementCodeGenVisitor(
						registry, typeMap, localStrategy, globalStrategy, processUID, fb, criticalSectionTracker, awaitAction));
			}
			actionAtLoopEnd.accept(fb);
		}
		// if the loop body has labels, we must not be in any critical condition after the loop
		// since loopConditionCriticalSectionTracker was used to end the critical section,
		//   it is not in any critical section
		// therefore, we can use it as criticalSectionTracker
		if (loopBodyHasLabel) {
			criticalSectionTracker = loopConditionCriticalSectionTracker;
		}
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		GoExpression condition = plusCalIf.getCondition().accept(
				new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy)
		);
		boolean containsLabels = plusCalIf.accept(new PlusCalStatementContainsLabelVisitor());
		try (GoIfBuilder b = builder.ifStmt(condition)) {
			CriticalSectionTracker noTracker = criticalSectionTracker.copy();
			try (GoBlockBuilder yes = b.whenTrue()) {
				for (PlusCalStatement stmt : plusCalIf.getYes()) {
					stmt.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, localStrategy, globalStrategy, processUID, yes, criticalSectionTracker, awaitAction));
				}
				// if an if statement contains a label, then the statement(s) after it must be labeled
				// if the statement after must be labeled, we know this critical section ends here (and
				// may be different between true and false branches). otherwise, leave the critical section
				// as is
				if (containsLabels) {
					criticalSectionTracker.end(yes);
				}
			}
			try (GoBlockBuilder no = b.whenFalse()) {
				for (PlusCalStatement stmt : plusCalIf.getNo()) {
					stmt.accept(new PlusCalStatementCodeGenVisitor(
							registry, typeMap, localStrategy, globalStrategy, processUID, no, noTracker, awaitAction));
				}
				// see description for true case
				if (containsLabels) {
					noTracker.end(no);
				}
			}
			criticalSectionTracker.checkCompatibility(noTracker);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		// track which local variable is written to
		Set<UID> localVarWrites = new HashSet<>();
		PlusCalStatementAtomicityInferenceVisitor writeTracker = new PlusCalStatementAtomicityInferenceVisitor(
				new UID(),
				(ignored1, ignored2) -> {},
				(expression, ignored) -> trackLocalVariableWrites(registry, localVarWrites, expression),
				new HashSet<>());
		List<List<PlusCalStatement>> cases = plusCalEither.getCases();
		for (List<PlusCalStatement> eitherCase : cases) {
			if (eitherCase.size() <= 0) {
				continue;
			}
			if (eitherCase.get(0) instanceof PlusCalLabeledStatements) {
				PlusCalStatement statement = eitherCase.get(0);
				// we only need to track the first labeled statements
				if (statement.accept(new PlusCalStatementContainsAwaitVisitor())) {
					statement.accept(writeTracker);
				}
			} else {
				// we only need to track up to, and excluding, the first labeled statements
				boolean foundAwait = false;
				PlusCalStatementContainsAwaitVisitor awaitChecker =
						new PlusCalStatementContainsAwaitVisitor(true);
				for (PlusCalStatement statement : eitherCase) {
					if (statement instanceof PlusCalLabeledStatements) {
						break;
					}
					foundAwait = foundAwait || statement.accept(awaitChecker);
				}
				if (foundAwait) {
					for (PlusCalStatement statement : eitherCase) {
						if (statement instanceof PlusCalLabeledStatements) {
							break;
						}
						statement.accept(writeTracker);
					}
				}
			}
		}
		// make copies of local variables which are in scope and are written to
		Map<GoVariableName, GoVariableName> localVarNames = new HashMap<>();
		for (UID varUID : localVarWrites) {
			if (builder.isInScope(varUID)) {
				GoVariableName name = builder.findUID(varUID);
				GoVariableName copyName = builder.varDecl(name.getName() + "Copy", name);
				localVarNames.put(name, copyName);
			}
		}
		// make copies of global variables which are written to
		Map<GoVariableName, GoVariableName> globalVarNames = new HashMap<>();
		for (UID varUID : registry.getVariableWritesInLockGroup(criticalSectionTracker.getCurrentLockGroup())) {
			GoVariableName name = builder.findUID(varUID);
			GoVariableName copyName = builder.varDecl(name.getName() + "Copy", name);
			globalVarNames.put(name, copyName);
		}
		// generate labels
		List<GoLabelName> labels = new ArrayList<>();
		for (int i = 0; i < cases.size(); i++) {
			labels.add(builder.newLabel("case" + Integer.toString(i)));
		}
		GoLabelName endEither = builder.newLabel("endEither");
		globalStrategy.registerNondeterminism(builder);
		// start codegen
		for (int i = 0; i < cases.size(); i++) {
			List<PlusCalStatement> eitherCase = cases.get(i);
			if (eitherCase.size() <= 0) {
				continue;
			}
			GoLabelName labelName = labels.get(i);
			builder.label(labelName);
			Function<GoBlockBuilder, GoLabelName> oldAwaitAction;
			CriticalSectionTracker tracker = criticalSectionTracker;
			PlusCalStatementCodeGenVisitor caseVisitor = this;
			if (i != 0) {
				// we arrived here via a failure of an await condition
				// restore the critical section back to when we first entered case 0
				criticalSectionTracker.restore(builder);
			}
			if (i != cases.size() - 1) {
				int j = i + 1;
				tracker = criticalSectionTracker.copy();
				caseVisitor = new PlusCalStatementCodeGenVisitor(
						registry, typeMap, localStrategy, globalStrategy, processUID, builder, tracker, builder -> {
					// restore variables
					localVarNames.forEach(builder::assign);
					globalVarNames.forEach(builder::assign);
					return labels.get(j);
				});
				oldAwaitAction = ignored -> null;
			} else {
				GoLabelName eitherLabel = tracker.getCurrentLabelName();
				if (eitherLabel == null) {
					throw new InternalCompilerError();
				}
				oldAwaitAction = awaitAction;
				awaitAction = builder -> {
					// restore variables
					localVarNames.forEach(builder::assign);
					globalVarNames.forEach(builder::assign);
					return eitherLabel;
				};
			}
			int nextIndex = 0;
			if (eitherCase.get(0) instanceof PlusCalLabeledStatements) {
				// we need to special case the first labeled statements
				eitherCase.get(0).accept(caseVisitor);
				nextIndex = 1;
			} else {
				// we need to special case statements up to, and excluding, the first labeled statements
				for (int k = 0; k < eitherCase.size(); k++, nextIndex = k) {
					PlusCalStatement statement = eitherCase.get(k);
					if (statement instanceof PlusCalLabeledStatements) {
						break;
					}
					statement.accept(caseVisitor);
				}
			}
			// codegen for the rest of the statements
			caseVisitor.awaitAction = oldAwaitAction;
			for (PlusCalStatement statement : eitherCase.subList(nextIndex, eitherCase.size())) {
				statement.accept(caseVisitor);
			}
			tracker.end(builder);
			if (i != cases.size() - 1) {
				builder.goTo(endEither);
			}
		}
		builder.label(endEither);
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<GoExpression> lhs = new ArrayList<>();
		List<GoExpression> rhs = new ArrayList<>();
		List<GlobalVariableStrategy.GlobalVariableWrite> lhsWrites = new ArrayList<>();
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			GlobalVariableStrategy.GlobalVariableWrite lhsWrite = pair.getLhs().accept(
					new TLAExpressionAssignmentLHSCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy));
			lhsWrites.add(lhsWrite);
			lhs.add(lhsWrite.getValueSink(builder));
			rhs.add(pair.getRhs().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy)));
		}
		builder.assign(lhs, rhs);
		for (GlobalVariableStrategy.GlobalVariableWrite lhsWrite : lhsWrites) {
			lhsWrite.writeAfter(builder);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		builder.addStatement(new GoReturn(Collections.emptyList()));
		return null;
	}

	@Override
	public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		// nothing to do here
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<GoExpression> arguments = new ArrayList<>();
		List<TLAExpression> args = plusCalCall.getArguments();
		for (int i = 0; i < args.size(); i++) {
			TLAExpression arg = args.get(i);
			GoExpression e = arg.accept(new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy));
			arguments.add(builder.varDecl("arg" + Integer.toString(i + 1), e));
		}
		// the critical section ends here because the procedure has to have a label on the first line of its body
		criticalSectionTracker.end(builder);
		builder.addStatement(new GoExpressionStatement(new GoCall(
				new GoVariableName(plusCalCall.getTarget()),
				arguments)));
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
		for(PlusCalVariableDeclaration decl : plusCalWith.getVariables()) {
			GoExpression value = decl.getValue().accept(
					new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy));
			if (decl.isSet()) {
				value = new GoIndexExpression(value, new GoIntLiteral(0));
			}
			builder.linkUID(decl.getUID(), builder.varDecl(decl.getName().getValue(), value));
		}
		for (PlusCalStatement statement : plusCalWith.getBody()) {
			statement.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		builder.print(plusCalPrint.getValue().accept(
				new TLAExpressionCodeGenVisitor(builder, registry, typeMap, localStrategy, globalStrategy)));
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		TLAExpression cond = plusCalAssert.getCondition();
		try (GoIfBuilder ifBuilder = builder.ifStmt(CodeGenUtil.invertCondition(
				builder, registry, typeMap, localStrategy, globalStrategy, cond))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				String msg = cond.toString();

				// since this is going to be in a string literal, we need to escape
				// potential backslashes in the operator to avoid confusing Go
				// there are any special characters in the string.
				msg = msg.replace("\\", "\\\\");
				yes.addPanic(new GoStringLiteral(msg));
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		TLAExpression cond = plusCalAwait.getCondition();
		try (GoIfBuilder ifBuilder = builder.ifStmt(CodeGenUtil.invertCondition(
				builder, registry, typeMap, localStrategy, globalStrategy, cond))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				// fork out an execution path for aborting
				CriticalSectionTracker tracker = criticalSectionTracker.copy();
				tracker.abort(yes, awaitAction.apply(yes));
			}
		}
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// fork out an execution path for this goto
		CriticalSectionTracker tracker = criticalSectionTracker.copy();
		// this critical section ends here
		tracker.end(builder);
		builder.goTo(new GoLabelName(plusCalGoto.getTarget()));
		// continue with the previous critical section
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}
