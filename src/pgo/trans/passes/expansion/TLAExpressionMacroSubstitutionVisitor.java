package pgo.trans.passes.expansion;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.tla.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class TLAExpressionMacroSubstitutionVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {

	private final IssueContext ctx;
	private final Map<String, TLAExpression> macroArgs;

	public TLAExpressionMacroSubstitutionVisitor(IssueContext ctx, Map<String, TLAExpression> macroArgs) {
		this.ctx= ctx;
		this.macroArgs = macroArgs;
	}
	
	private List<TLAGeneralIdentifierPart> substitutePrefix(List<TLAGeneralIdentifierPart> prefix){
		List<TLAGeneralIdentifierPart> result = new ArrayList<>();
		for(TLAGeneralIdentifierPart part : prefix) {
			// TODO: what would TLC do if the identifier part's name matched an argument?
			result.add(new TLAGeneralIdentifierPart(part.getLocation(), part.getIdentifier().copy(),
					part.getParameters().stream().map(p -> p.accept(this)).collect(Collectors.toList())));
		}
		return result;
	}
	
	private List<TLAQuantifierBound> substituteQuantifierBounds(List<TLAQuantifierBound> bounds){
		List<TLAQuantifierBound> result = new ArrayList<>();
		for(TLAQuantifierBound qb : bounds) {
			List<TLAIdentifier> ids = substituteIdentifiers(qb.getIds());
			result.add(new TLAQuantifierBound(qb.getLocation(), qb.getType(), ids, qb.getSet().accept(this)));
		}
		return result;
	}
	
	private List<TLAIdentifier> substituteIdentifiers(List<TLAIdentifier> ids){
		for(TLAIdentifier id : ids) {
			if(macroArgs.containsKey(id.getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(id));
			}
		}
		return ids;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		return new TLAFunctionCall(tlaFunctionCall.getLocation(), tlaFunctionCall.getFunction().accept(this),
				tlaFunctionCall.getParams().stream().map(p -> p.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLABinOp tlaBinOp) throws RuntimeException {
		TLABinOp result = new TLABinOp(tlaBinOp.getLocation(), tlaBinOp.getOperation(),
				substitutePrefix(tlaBinOp.getPrefix()), tlaBinOp.getLHS().accept(this),
				tlaBinOp.getRHS().accept(this));
		result.setRefersTo(tlaBinOp.getRefersTo());
		return result;
	}

	@Override
	public TLAExpression visit(TLABool tlaBool) throws RuntimeException {
		return tlaBool.copy();
	}

	@Override
	public TLAExpression visit(TLACase tlaCase) throws RuntimeException {
		return new TLACase(
				tlaCase.getLocation(),
				tlaCase.getArms().stream().map(arm ->
						new TLACaseArm(
								arm.getLocation(),
								arm.getCondition().accept(this),
								arm.getResult().accept(this))).collect(Collectors.toList()),
				tlaCase.getOther() != null ? tlaCase.getOther().accept(this) : null);
	}

	@Override
	public TLAExpression visit(TLADot tlaDot) throws RuntimeException {
		return new TLADot(tlaDot.getLocation(), tlaDot.getExpression().accept(this), tlaDot.getField());
	}

	@Override
	public TLAExpression visit(TLAExistential tlaExistential) throws RuntimeException {
		return new TLAExistential(tlaExistential.getLocation(), substituteIdentifiers(tlaExistential.getIds()),
				tlaExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunction tlaFunction) throws RuntimeException {
		return new TLAFunction(tlaFunction.getLocation(), substituteQuantifierBounds(tlaFunction.getArguments()),
				tlaFunction.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		return new TLAFunctionSet(tlaFunctionSet.getLocation(), tlaFunctionSet.getFrom().accept(this), tlaFunctionSet.getTo().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		return new TLAFunctionSubstitution(
				tlaFunctionSubstitution.getLocation(),
				tlaFunctionSubstitution.getSource().accept(this),
				tlaFunctionSubstitution.getSubstitutions().stream().map(pair -> {
					return new TLAFunctionSubstitutionPair(
							pair.getLocation(),
							pair.getKeys().stream().map(TLASubstitutionKey::copy).collect(Collectors.toList()),
							pair.getValue().accept(this));
				}).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLAIf tlaIf) throws RuntimeException {
		return new TLAIf(tlaIf.getLocation(), tlaIf.getCond().accept(this), tlaIf.getTval().accept(this), tlaIf.getFval().accept(this));
	}

	@Override
	public TLAExpression visit(TLALet tlaLet) throws RuntimeException {
		return new TLALet(tlaLet.getLocation(), null, tlaLet.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		if(tlaGeneralIdentifier.getGeneralIdentifierPrefix().isEmpty()) {
			if(macroArgs.containsKey(tlaGeneralIdentifier.getName().getId())) {
				return macroArgs.get(tlaGeneralIdentifier.getName().getId());
			}
		}else {
			if(macroArgs.containsKey(tlaGeneralIdentifier.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(tlaGeneralIdentifier.getName()));
			}
		}
		TLAGeneralIdentifier result = new TLAGeneralIdentifier(tlaGeneralIdentifier.getLocation(), tlaGeneralIdentifier.getName(),
				substitutePrefix(tlaGeneralIdentifier.getGeneralIdentifierPrefix()));
		result.setRefersTo(tlaGeneralIdentifier.getRefersTo());
		return result;
	}

	@Override
	public TLAExpression visit(TLATuple tlaTuple) throws RuntimeException {
		return new TLATuple(tlaTuple.getLocation(), tlaTuple.getElements().stream().map(e -> e.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		return new TLAMaybeAction(tlaMaybeAction.getLocation(), tlaMaybeAction.getBody().accept(this), tlaMaybeAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLANumber tlaNumber) throws RuntimeException {
		return tlaNumber.copy();
	}

	@Override
	public TLAExpression visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		if(macroArgs.containsKey(tlaOperatorCall.getName().getId())) {
			ctx.error(new MacroArgumentInnerScopeConflictIssue(tlaOperatorCall.getName()));
		}
		TLAOperatorCall result = new TLAOperatorCall(tlaOperatorCall.getLocation(),
				tlaOperatorCall.getName(),
				substitutePrefix(tlaOperatorCall.getPrefix()),
				tlaOperatorCall.getArgs().stream().map(a -> a.accept(this)).collect(Collectors.toList()));
		result.setRefersTo(tlaOperatorCall.getRefersTo());
		return result;
	}

	@Override
	public TLAExpression visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		return new TLAQuantifiedExistential(tlaQuantifiedExistential.getLocation(),
				substituteQuantifierBounds(tlaQuantifiedExistential.getIds()),
				tlaQuantifiedExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		return new TLAQuantifiedUniversal(tlaQuantifiedUniversal.getLocation(),
				substituteQuantifierBounds(tlaQuantifiedUniversal.getIds()),
				tlaQuantifiedUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		return new TLARecordConstructor(tlaRecordConstructor.getLocation(), tlaRecordConstructor.getFields().stream().map(field -> {
			if(macroArgs.containsKey(field.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(field.getName()));
			}
			return new TLARecordConstructor.Field(field.getLocation(), field.getName(), field.getValue().accept(this));
		}).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		return new TLARecordSet(tlaRecordSet.getLocation(), tlaRecordSet.getFields().stream().map(field -> {
			if(macroArgs.containsKey(field.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(field.getName()));
			}
			return new TLARecordSet.Field(field.getLocation(), field.getName().copy(), field.getSet().accept(this));
		}).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		return new TLARequiredAction(
				tlaRequiredAction.getLocation(),
				tlaRequiredAction.getBody().accept(this),
				tlaRequiredAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		return new TLASetConstructor(tlaSetConstructor.getLocation(),
				tlaSetConstructor.getContents().stream().map(c -> c.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		return new TLASetComprehension(tlaSetComprehension.getLocation(),
				tlaSetComprehension.getBody().accept(this), substituteQuantifierBounds(tlaSetComprehension.getBounds()));
	}

	@Override
	public TLAExpression visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		TLAIdentifierOrTuple ident = tlaSetRefinement.getIdent();
		if(ident.isTuple()) {
			substituteIdentifiers(ident.getTuple());
		}else {
			if(macroArgs.containsKey(ident.getId().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(ident.getId()));
			}
		}
		return new TLASetRefinement(
				tlaSetRefinement.getLocation(),
				new TLAQuantifierBound(
						tlaSetRefinement.getBinding().getLocation(),
						tlaSetRefinement.getBinding().getType(),
						tlaSetRefinement.getBinding().getIds(),
						tlaSetRefinement.getBinding().getSet().accept(this)),
				tlaSetRefinement.getWhen().accept(this));
	}

	@Override
	public TLAExpression visit(TLAString tlaString) throws RuntimeException {
		return tlaString.copy();
	}

	@Override
	public TLAExpression visit(TLAUnary tlaUnary) throws RuntimeException {
		TLAUnary result = new TLAUnary(tlaUnary.getLocation(), tlaUnary.getOperation(), substitutePrefix(tlaUnary.getPrefix()),
				tlaUnary.getOperand().accept(this));
		result.setRefersTo(tlaUnary.getRefersTo());
		return result;
	}

	@Override
	public TLAExpression visit(TLAUniversal tlaUniversal) throws RuntimeException {
		return new TLAUniversal(tlaUniversal.getLocation(), substituteIdentifiers(tlaUniversal.getIds()), tlaUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return plusCalDefaultInitValue.copy();
	}

	@Override
	public TLAExpression visit(TLAFairness fairness) throws RuntimeException {
		return new TLAFairness(
				fairness.getLocation(), fairness.getType(), fairness.getVars().accept(this),
				fairness.getExpression().accept(this));
	}

	@Override
	public TLAExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public TLAExpression visit(TLARef tlaRef) throws RuntimeException {
		// nothing to do here
		return tlaRef;
	}

}
