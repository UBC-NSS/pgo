package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.Unreachable;
import pgo.model.golang.GoExpression;
import pgo.model.golang.GoLabelName;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.pcal.PlusCalProcess;
import pgo.model.tla.TLAExpression;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.CriticalSection;

import java.util.HashMap;
import java.util.Map;

public abstract class GlobalVariableStrategy implements CriticalSection {
	private Map<UID, GoVariableName> variables = new HashMap<>();

	protected void addVariable(UID uid, GoVariableName variableName) {
		if (variables.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		variables.put(uid, variableName);
	}

	protected GoVariableName findVariable(UID uid) {
		if (!variables.containsKey(uid)) {
			throw new InternalCompilerError();
		}
		return variables.get(uid);
	}

	/**
	 * 	Called at the beginning of an either, to allow ArchetypeResourceGlobalVariableStrategy to statically disallow
	 * 	any blocking actions that might interfere with the liveness of trying each execution path one by one: any one
	 * 	path may not do anything that indefinitely holds up the others.
 	 */
	public abstract void registerNondeterminism(GoBlockBuilder builder);

	public abstract void initPostlude(GoModuleBuilder moduleBuilder, GoBlockBuilder initBuilder);

	public abstract void processPrelude(GoBlockBuilder processBody, PlusCalProcess process, String processName, GoVariableName self, GoType selfType);

	public abstract void mainPrelude(GoBlockBuilder builder);

	@Override
	public abstract void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName);

	@Override
	public abstract void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName);

	@Override
	public abstract void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName);

	public GoExpression readArchetypeResource(GoBlockBuilder builder, TLAExpression expression) {
		throw new Unreachable();
	}

	public GlobalVariableWrite writeArchetypeResource(GoBlockBuilder builder, TLAExpression expression) {
		throw new Unreachable();
	}

	public abstract GoExpression readGlobalVariable(GoBlockBuilder builder, UID uid);

	public interface GlobalVariableWrite {
		GoExpression getValueSink(GoBlockBuilder builder);
		void writeAfter(GoBlockBuilder builder);
	}

	public abstract GlobalVariableWrite writeGlobalVariable(UID uid);

	// map global variables to locals
	// commit on success
	// rollback on failure
	// inputs to strategy:
	// - variables to read
	// - variables to write
	// - when a section starts
	// - when a section ends
	// - when a section rolls back
	// - ability to inform global var lookups and sets
}
