package pgo.trans.passes.codegen;

import pgo.InternalCompilerError;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.GoLabelName;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.function.Consumer;

public class CriticalSectionTracker {
	private DefinitionRegistry registry;
	private UID processUID;
	private CriticalSection criticalSection;
	private int currentLockGroup;
	private UID currentLabelUID;
	private GoLabelName currentLabelName;

	private CriticalSectionTracker(DefinitionRegistry registry, UID processUID, CriticalSection criticalSection,
	                               int currentLockGroup, UID currentLabelUID, GoLabelName currentLabelName) {
		this.registry = registry;
		this.processUID = processUID;
		this.criticalSection = criticalSection;
		this.currentLockGroup = currentLockGroup;
		this.currentLabelUID = currentLabelUID;
		this.currentLabelName = currentLabelName;
	}

	public CriticalSectionTracker(DefinitionRegistry registry, UID processUID, CriticalSection criticalSection) {
		this(registry, processUID, criticalSection, -1, null, null);
	}

	public void start(GoBlockBuilder builder, UID labelUID, GoLabelName labelName) {
		int lockGroup = registry.getLockGroupOrDefault(labelUID, -1);
		if (currentLockGroup != -1 && currentLockGroup != lockGroup) {
			end(builder);
		}
		if (currentLockGroup == lockGroup) {
			// nothing to do
			return;
		}
		builder.labelIsUnique(labelName.getName());
		criticalSection.startCriticalSection(builder, processUID, lockGroup, labelUID, labelName);
		currentLockGroup = lockGroup;
		currentLabelUID = labelUID;
		currentLabelName = labelName;
	}

	public void abort(GoBlockBuilder builder) {
		if (currentLockGroup > -1) {
			criticalSection.abortCriticalSection(
					builder, processUID, currentLockGroup, currentLabelUID, currentLabelName);
		}
		builder.goTo(currentLabelName);
		currentLockGroup = -1;
		currentLabelUID = null;
		currentLabelName = null;
	}

	public void end(GoBlockBuilder builder) {
		if (currentLockGroup == -1) {
			// nothing to do
			return;
		}
		criticalSection.endCriticalSection(builder, processUID, currentLockGroup, currentLabelUID, currentLabelName);
		currentLockGroup = -1;
		currentLabelUID = null;
		currentLabelName = null;
	}

	public void checkCompatibility(CriticalSectionTracker other) {
		if (registry != other.registry || criticalSection != other.criticalSection ||
				currentLockGroup != other.currentLockGroup || currentLabelUID != other.currentLabelUID ||
				(currentLabelName != null && !currentLabelName.getName().equals(other.currentLabelName.getName()))) {
			throw new InternalCompilerError();
		}
	}

	public CriticalSectionTracker copy() {
		return new CriticalSectionTracker(
				registry, processUID, criticalSection, currentLockGroup, currentLabelUID, currentLabelName);
	}

	public Consumer<GoBlockBuilder> actionAtLoopEnd() {
		// since we're compiling while loops to infinite loops with a conditional break, we have to reacquire
		// the critical section at loop end
		int lockGroup = currentLockGroup;
		UID labelUID = currentLabelUID;
		GoLabelName labelName = currentLabelName;
		if (lockGroup < 0) {
			return ignored -> {};
		}
		return builder -> start(builder, labelUID, labelName);
	}
}
