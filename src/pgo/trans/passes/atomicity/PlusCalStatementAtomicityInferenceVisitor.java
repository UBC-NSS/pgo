package pgo.trans.passes.atomicity;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.scope.UID;

import java.util.Set;
import java.util.function.BiConsumer;

public class PlusCalStatementAtomicityInferenceVisitor extends PlusCalStatementVisitor<Void, RuntimeException> {
	private final UID currentLabelUID;
	private final BiConsumer<TLAExpression, UID> captureLabelRead;
	private final BiConsumer<TLAExpression, UID> captureLabelWrite;
	private final Set<UID> foundLabels;
	private final TLAExpressionValueAtomicityInferenceVisitor visitor;

	public PlusCalStatementAtomicityInferenceVisitor(UID currentLabelUID, BiConsumer<TLAExpression, UID> captureLabelRead,
	                                                 BiConsumer<TLAExpression, UID> captureLabelWrite, Set<UID> foundLabels) {
		this.currentLabelUID = currentLabelUID;
		this.captureLabelRead = captureLabelRead;
		this.captureLabelWrite = captureLabelWrite;
		this.foundLabels = foundLabels;
		this.visitor = new TLAExpressionValueAtomicityInferenceVisitor(expression ->
				captureLabelRead.accept(expression, currentLabelUID));
	}

	@Override
	public Void visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		UID labelUID = plusCalLabeledStatements.getLabel().getUID();
		foundLabels.add(labelUID);
		PlusCalStatementAtomicityInferenceVisitor statementVisitor = new PlusCalStatementAtomicityInferenceVisitor(
				labelUID, captureLabelRead, captureLabelWrite, foundLabels);
		plusCalLabeledStatements.getStatements().forEach(s -> s.accept(statementVisitor));
		return null;
	}

	@Override
	public Void visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		plusCalWhile.getCondition().accept(visitor);
		plusCalWhile.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalIf plusCalIf) throws RuntimeException {
		plusCalIf.getCondition().accept(visitor);
		plusCalIf.getYes().forEach(s -> s.accept(this));
		plusCalIf.getNo().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalEither plusCalEither) throws RuntimeException {
		plusCalEither.getCases().forEach(c -> c.forEach(s -> s.accept(this)));
		return null;
	}

	@Override
	public Void visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			pair.getLhs().accept(new TLAExpressionLHSAtomicityInferenceVisitor(
					visitor, varUID -> captureLabelWrite.accept(varUID, currentLabelUID)));
			pair.getRhs().accept(visitor);
		}
		return null;
	}

	@Override
	public Void visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(PlusCalCall plusCalCall) throws RuntimeException {
		plusCalCall.getArguments().forEach(a -> a.accept(visitor));
		return null;
	}

	@Override
	public Void visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalWith plusCalWith) throws RuntimeException {
		for (PlusCalVariableDeclaration decl : plusCalWith.getVariables()) {
			decl.getValue().accept(visitor);
		}
		plusCalWith.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		plusCalPrint.getValue().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		plusCalAssert.getCondition().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		plusCalAwait.getCondition().accept(visitor);
		return null;
	}

	@Override
	public Void visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new TODO();
	}
}
