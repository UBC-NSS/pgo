package pgo.trans.passes.codegen.go;

import pgo.PGoNetOptions;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.builder.GoSwitchBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.model.pcal.PlusCalProcess;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.stream.Collectors;

public class StateServerGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, Type> typeMap;
	private PGoNetOptions.StateOptions stateOptions;
	private ModularPlusCalBlock modularPlusCalBlock;
	private GoCommandLineArgumentParser commandLineArgumentParser;
	private UID processNameUID;
	private UID processArgumentUID;
	private UID errUID;
	private UID globalStateUID;
	private UID refsUID;

	public StateServerGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, Type> typeMap,
	                                         PGoNetOptions.StateOptions stateOptions,
	                                         ModularPlusCalBlock modularPlusCalBlock) {
		this.registry = registry;
		this.typeMap = typeMap;
		this.stateOptions = stateOptions;
		this.modularPlusCalBlock = modularPlusCalBlock;
		this.commandLineArgumentParser = new GoCommandLineArgumentParser();
		this.processNameUID = new UID();
		this.processArgumentUID = new UID();
		this.errUID = new UID();
		this.globalStateUID = new UID();
		this.refsUID = new UID();
	}

	static void generateProcessSwitch(Map<UID, Type> typeMap, ModularPlusCalBlock modularPlusCalBlock,
	                                  GoBlockBuilder builder, GoVariableName processName,
	                                  GoVariableName processArgument) {
		try (GoSwitchBuilder switchBuilder = builder.switchStmt(processName)) {
			for (PlusCalProcess process : ((PlusCalMultiProcess) modularPlusCalBlock.getProcesses()).getProcesses()) {
				String name = process.getName().getName().getValue();
				GoType type = typeMap.get(process.getName().getUID()).accept(new TypeConversionVisitor());
				try (GoBlockBuilder caseBody = switchBuilder.addCase(new GoStringLiteral(name))) {
					if (type.equals(GoBuiltins.Int)) {
						builder.addImport("strconv");
						List<GoVariableName> names = caseBody.varDecl(
								Arrays.asList("i", "err"),
								new GoCall(
										new GoSelectorExpression(new GoVariableName("strconv"), "Atoi"),
										Collections.singletonList(processArgument)));
						GoVariableName i = names.get(0);
						GoVariableName err = names.get(1);
						try (GoIfBuilder ifBuilder = caseBody.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
							try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
								yes.addPanic(new GoBinop(
										GoBinop.Operation.PLUS,
										new GoStringLiteral("Process " + name +
												" requires an integer argument; err = "),
										new GoCall(new GoSelectorExpression(err, "Error"), Collections.emptyList())));
							}
						}
						caseBody.addStatement(new GoCall(new GoVariableName(name), Collections.singletonList(i)));
					} else if (type.equals(GoBuiltins.String)) {
						caseBody.addStatement(new GoCall(
								new GoVariableName(name),
								Collections.singletonList(processArgument)));
					} else {
						throw new Unreachable();
					}
				}
			}
			try (GoBlockBuilder defaultCaseBody = switchBuilder.defaultCase()) {
				defaultCaseBody.addPanic(new GoBinop(
						GoBinop.Operation.PLUS,
						new GoStringLiteral("Unknown process "),
						processName));
			}
		}
	}

	private void releaseRefs(GoBlockBuilder builder) {
		GoVariableName refs = findVariable(refsUID);
		GoVariableName err = findVariable(errUID);
		builder.assign(err, new GoCall(
				new GoSelectorExpression(findVariable(globalStateUID), "Release"),
				Collections.singletonList(refs)));
		try (GoIfBuilder ifBuilder = builder.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
	}

	@Override
	public void registerNondeterminism(GoBlockBuilder builder) {
		// pass
	}

	@Override
	public void initPostlude(GoModuleBuilder moduleBuilder, GoBlockBuilder initBuilder) {
		GoVariableName processName = moduleBuilder.defineGlobal(processNameUID, "processName", GoBuiltins.String);
		addVariable(processNameUID, processName);
		GoVariableName processArgument = moduleBuilder.defineGlobal(processArgumentUID, "processArgument", GoBuiltins.String);
		addVariable(processArgumentUID, processArgument);
		commandLineArgumentParser.addPositionalArgument("processPlusArgument", "processName(processArgument)");
		commandLineArgumentParser.addPositionalArgument("ipPort", "ip:port");
		List<GoVariableName> commandLineArguments = commandLineArgumentParser.generateArgumentParsingCode(initBuilder);
		GoVariableName processPlusArgument = commandLineArguments.get(0);
		GoVariableName ipPort = commandLineArguments.get(1);
		CodeGenUtil.generateArgumentParsing(initBuilder, processPlusArgument, processName, processArgument);

		moduleBuilder.addImport("pgo/distsys");
		GoVariableName err = moduleBuilder.defineGlobal(errUID, "err", GoBuiltins.Error);
		addVariable(errUID, err);
		GoVariableName globalState = moduleBuilder.defineGlobal(
				globalStateUID, "globalState", new GoPtrType(new GoTypeName("distsys.StateServer")));
		addVariable(globalStateUID, globalState);
		GoVariableName peers = initBuilder.varDecl(
				"peers",
				new GoSliceLiteral(GoBuiltins.String, stateOptions.peers.stream()
						.map(GoStringLiteral::new)
						.collect(Collectors.toList())));
		GoVariableName coordinator = initBuilder.varDecl("coordinator", new GoIndexExpression(peers, new GoIntLiteral(0)));
		initBuilder.assign(
				Arrays.asList(globalState, err),
				new GoCall(
						new GoSelectorExpression(new GoVariableName("distsys"), "NewStateServer"),
						Arrays.asList(
								processPlusArgument,
								peers,
								ipPort,
								coordinator,
								new GoMapLiteral(
										GoBuiltins.String,
										GoBuiltins.Interface,
										new HashMap<GoExpression, GoExpression>() {{
											for (UID varUID : registry.protectedGlobalVariables()) {
												GoVariableName variableName = initBuilder.findUID(varUID);
												put(new GoStringLiteral(variableName.getName()), variableName);
											}
										}}),
								new GoCall(
										new GoSelectorExpression(new GoVariableName("distsys"), "NewRandomMigrate"),
										Collections.singletonList(ipPort)))));
		try (GoIfBuilder ifBuilder = initBuilder.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
		GoVariableName refs = moduleBuilder.defineGlobal(
				refsUID, "refs", new GoTypeName("distsys.VarReferences"));
		addVariable(refsUID, refs);
	}

	@Override
	public void processPrelude(GoBlockBuilder processBody, PlusCalProcess process, String processName, GoVariableName self, GoType selfType) {
		// nothing to do
	}

	@Override
	public void mainPrelude(GoBlockBuilder builder) {
		GoVariableName err = findVariable(errUID);
		builder.assign(
				err,
				new GoCall(new GoSelectorExpression(findVariable(globalStateUID), "WaitPeers"), Collections.emptyList()));
		try (GoIfBuilder ifBuilder = builder.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
		generateProcessSwitch(
				typeMap, modularPlusCalBlock, builder, findVariable(processNameUID), findVariable(processArgumentUID));
		builder.assign(
				err,
				new GoCall(new GoSelectorExpression(findVariable(globalStateUID), "WaitPeers"), Collections.emptyList()));
		try (GoIfBuilder ifBuilder = builder.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
	}

	@Override
	public void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		Set<UID> readSet = new HashSet<>(registry.getVariableReadsInLockGroup(lockGroup));
		Set<UID> writeSet = registry.getVariableWritesInLockGroup(lockGroup);
		readSet.removeAll(writeSet);
		ArrayList<UID> readVariableUIDs = new ArrayList<>(readSet);
		List<GoVariableName> readVariableNames = readVariableUIDs.stream().map(builder::findUID).collect(Collectors.toList());
		List<GoExpression> readVariableNameStrings = readVariableNames.stream()
				.map(v -> new GoStringLiteral(v.getName()))
				.collect(Collectors.toList());
		ArrayList<UID> writeVariableUIDs = new ArrayList<>(writeSet);
		List<GoVariableName> writeVariableNames = writeVariableUIDs.stream().map(builder::findUID).collect(Collectors.toList());
		List<GoExpression> writeVariableNameStrings = writeVariableNames.stream()
				.map(v -> new GoStringLiteral(v.getName()))
				.collect(Collectors.toList());
		GoVariableName refs = findVariable(refsUID);
		GoVariableName err = findVariable(errUID);
		builder.assign(
				Arrays.asList(refs, err),
				new GoCall(
						new GoSelectorExpression(findVariable(globalStateUID), "Acquire"),
						Collections.singletonList(new GoUnary(
								GoUnary.Operation.ADDR,
								new GoStructLiteral(
										new GoTypeName("distsys.BorrowSpec"),
										Arrays.asList(
												new GoStructLiteralField(
														"ReadNames",
														new GoSliceLiteral(GoBuiltins.String, readVariableNameStrings)),
												new GoStructLiteralField(
														"WriteNames",
														new GoSliceLiteral(GoBuiltins.String, writeVariableNameStrings))))))));
		try (GoIfBuilder ifBuilder = builder.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
		// pull all values out of the map and into globals
		for (int i = 0; i < writeVariableNames.size(); i++) {
			builder.assign(
					writeVariableNames.get(i),
					new GoTypeAssertion(
							new GoCall(
									new GoSelectorExpression(refs, "Get"),
									Collections.singletonList(new GoStringLiteral(writeVariableNames.get(i).getName()))),
							registry.getGlobalVariableType(writeVariableUIDs.get(i))));
		}
		for (int i = 0; i < readVariableNames.size(); i++) {
			builder.assign(
					readVariableNames.get(i),
					new GoTypeAssertion(
							new GoCall(
									new GoSelectorExpression(refs, "Get"),
									Collections.singletonList(new GoStringLiteral(readVariableNames.get(i).getName()))),
							registry.getGlobalVariableType(readVariableUIDs.get(i))));
		}
	}

	@Override
	public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		releaseRefs(builder);
	}

	@Override
	public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		GoVariableName refs = findVariable(refsUID);
		for (UID varUID : registry.getVariableWritesInLockGroup(lockGroup)) {
			GoVariableName name = builder.findUID(varUID);
			builder.addStatement(new GoCall(
					new GoSelectorExpression(refs, "Set"),
					Arrays.asList(new GoStringLiteral(name.getName()), name)));
		}
		releaseRefs(builder);
	}

	@Override
	public GoExpression readGlobalVariable(GoBlockBuilder builder, UID uid) {
		return builder.findUID(uid);
	}

	@Override
	public GlobalVariableWrite writeGlobalVariable(UID uid) {
		return new GlobalVariableWrite() {
			@Override
			public GoExpression getValueSink(GoBlockBuilder builder) {
				return builder.findUID(uid);
			}

			@Override
			public void writeAfter(GoBlockBuilder builder) {

			}
		};
	}
}
