package pgo.trans.passes.codegen.go;

import pgo.PGoNetOptions;
import pgo.Unreachable;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalProcess;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.stream.Collectors;

public class EtcdGlobalVariableStrategy extends GlobalVariableStrategy {
	private DefinitionRegistry registry;
	private Map<UID, Type> typeMap;
	private PGoNetOptions.StateOptions stateOptions;
	private ModularPlusCalBlock modularPlusCalBlock;
	private GoCommandLineArgumentParser commandLineArgumentParser;
	private UID processNameUID;
	private UID processArgumentUID;
	private UID errUID;
	private UID globalStateUID;

	public EtcdGlobalVariableStrategy(DefinitionRegistry registry, Map<UID, Type> typeMap,
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
				globalStateUID, "globalState", new GoPtrType(new GoTypeName("distsys.EtcdState")));
		addVariable(globalStateUID, globalState);
		GoVariableName peers = initBuilder.varDecl(
				"peers",
				new GoSliceLiteral(
						GoBuiltins.String,
						stateOptions.peers.stream().map(GoStringLiteral::new) .collect(Collectors.toList())));
		GoVariableName coordinator = initBuilder.varDecl("coordinator", new GoIndexExpression(peers, new GoIntLiteral(0)));
		initBuilder.assign(
				Arrays.asList(globalState, err),
				new GoCall(
						new GoSelectorExpression(new GoVariableName("distsys"), "NewEtcdState"),
						Arrays.asList(
								new GoSliceLiteral(
										GoBuiltins.String,
										stateOptions.endpoints.stream()
												.map(e -> new GoStringLiteral("http://" + e))
												.collect(Collectors.toList())),
								new GoIntLiteral(stateOptions.timeout),
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
										}}))));
		try (GoIfBuilder ifBuilder = initBuilder.ifStmt(new GoBinop(GoBinop.Operation.NEQ, err, GoBuiltins.Nil))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.addPanic(err);
			}
		}
	}

	@Override
	public void processPrelude(GoBlockBuilder processBody, PlusCalProcess process, String processName, GoVariableName self, GoType selfType) {
		GoVariableName selfStr;
		if (selfType.equals(GoBuiltins.Int)) {
			// selfStr := "processName(" + strconv.Itoa(self) + ")"
			processBody.addImport("strconv");
			selfStr = processBody.varDecl(
					"selfStr",
					new GoBinop(
							GoBinop.Operation.PLUS,
							new GoBinop(
									GoBinop.Operation.PLUS,
									new GoStringLiteral(processName + "("),
									new GoCall(
											new GoSelectorExpression(new GoVariableName("strconv"), "Itoa"),
											Collections.singletonList(self))),
							new GoStringLiteral(")")));
		} else if (selfType.equals(GoBuiltins.String)) {
			// selfStr := "processName(" + self + ")"
			selfStr = processBody.varDecl(
					"selfStr",
					new GoBinop(
							GoBinop.Operation.PLUS,
							new GoBinop(
									GoBinop.Operation.PLUS,
									new GoStringLiteral(processName + "("),
									self),
							new GoStringLiteral(")")));
		} else {
			throw new Unreachable();
		}
		addVariable(process.getName().getUID(), selfStr);
	}

	@Override
	public void registerNondeterminism(GoBlockBuilder builder) {
		// pass
	}

	@Override
	public void mainPrelude(GoBlockBuilder builder) {
		StateServerGlobalVariableStrategy.generateProcessSwitch(
				typeMap, modularPlusCalBlock, builder, findVariable(processNameUID), findVariable(processArgumentUID));
	}

	@Override
	public void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		Set<UID> readSet = new HashSet<>(registry.getVariableReadsInLockGroup(lockGroup));
		Set<UID> writeSet = registry.getVariableWritesInLockGroup(lockGroup);
		readSet.removeAll(writeSet);
		GoVariableName globalState = findVariable(globalStateUID);
		builder.addStatement(new GoCall(
				new GoSelectorExpression(findVariable(globalStateUID), "Lock"),
				Arrays.asList(findVariable(processUID), new GoStringLiteral(Integer.toString(lockGroup)))));
		for (UID varUID : writeSet) {
			GoVariableName variableName = builder.findUID(varUID);
			builder.addStatement(new GoCall(
					new GoSelectorExpression(globalState, "Get"),
					Arrays.asList(
							new GoStringLiteral(variableName.getName()),
							new GoUnary(GoUnary.Operation.ADDR, variableName))));
		}
		for (UID varUID : readSet) {
			GoVariableName variableName = builder.findUID(varUID);
			builder.addStatement(new GoCall(
					new GoSelectorExpression(globalState, "Get"),
					Arrays.asList(
							new GoStringLiteral(variableName.getName()),
							new GoUnary(GoUnary.Operation.ADDR, variableName))));
		}
	}

	@Override
	public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		builder.addStatement(new GoCall(
				new GoSelectorExpression(findVariable(globalStateUID), "Unlock"),
				Arrays.asList(findVariable(processUID), new GoStringLiteral(Integer.toString(lockGroup)))));
	}

	@Override
	public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
		GoVariableName globalState = findVariable(globalStateUID);
		for (UID varUID : registry.getVariableWritesInLockGroup(lockGroup)) {
			GoVariableName variableName = builder.findUID(varUID);
			builder.addStatement(new GoCall(
					new GoSelectorExpression(globalState, "Set"),
					Arrays.asList(
							new GoStringLiteral(variableName.getName()),
							variableName)));
		}
		builder.addStatement(new GoCall(
				new GoSelectorExpression(findVariable(globalStateUID), "Unlock"),
				Arrays.asList(findVariable(processUID), new GoStringLiteral(Integer.toString(lockGroup)))));
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
