package pgo.model.golang.builder;

import pgo.model.golang.GoExpression;
import pgo.model.golang.GoForRange;
import pgo.model.golang.GoVariableName;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.scope.UID;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class GoForRangeBuilder {
	private final GoASTBuilder parent;
	private final NameCleaner nameCleaner;
	private final Map<UID, GoVariableName> nameMap;
	private final NameCleaner labelScope;

	private final List<GoExpression> lhs;
	private final GoExpression rangeExpr;

	public GoForRangeBuilder(GoASTBuilder parent, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap, NameCleaner labelScope, GoExpression rangeExpr) {
		this.parent = parent;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		this.labelScope = labelScope;
		this.rangeExpr = rangeExpr;
		this.lhs = new ArrayList<>();
	}

	public List<GoVariableName> initVariables(List<String> nameHints) {
		List<GoVariableName> names = new ArrayList<>();
		for (String nameHint : nameHints) {
			String actualName = nameCleaner.cleanName(nameHint);
			GoVariableName name = new GoVariableName(actualName);
			names.add(name);
			lhs.add(name);
		}
		return names;
	}

	public GoBlockBuilder getBlockBuilder() {
		return new GoBlockBuilder(parent, nameCleaner, nameMap, labelScope, block ->
				parent.addStatement(new GoForRange(lhs, true, rangeExpr, block)));
	}
}
