package dashboard;

import static java.util.stream.Collectors.joining;

import java.io.File;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeOptimization;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.extension.Extension;
import constraints.intension.Intension;
import dashboard.Control.SettingVars;
import interfaces.Observers.ObserverConstruction;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import learning.IpsRecorder;
import learning.IpsRecorderForEquivalence;
import learning.ReductionOperator;
import main.Head;
import optimization.Optimizer;
import problem.Features;
import propagation.GAC;
import propagation.Propagation;
import propagation.SAC;
import propagation.SAC.SACGreedy;
import solver.Statistics;
import utility.Enums.EStopping;
import utility.Enums.TypeOutput;
import utility.Kit;
import variables.Variable;

/**
 * The role of this class is to output data concerning the resolution of problem instances. These data are collected by means of an XML document that may be
 * saved. A part of the data are also directly displayed on the standard output.
 * 
 * @author Christophe Lecoutre
 */
public class Output implements ObserverConstruction, ObserverSearch, ObserverRuns {

	/**********************************************************************************************
	 * Constants
	 *********************************************************************************************/

	public static final String RESULTS_DIRECTORY = "results";
	public static final String SETTINGS_DIRECTORY = "configurations";
	public static final String CONTEXT_DIRECTORY = "context";
	public static final String MULTITHREAD_RESULTS = "multithreadResults";
	public static final String CONFIGURATION_FILE_NAME = "configurationFileName";
	public static final String TOTAL_WCK_TIME = "totalWckTime";

	public static final String INSTANCE = "Instance";
	public static final String DOMAINS = "Domains";
	public static final String VARIABLES = "Variables";
	public static final String CONSTRAINTS = "Constraints";
	public static final String OBJECTIVE = "Objective";
	public static final String SOLVER = "Solver";
	public static final String PREPROCESSING = "Preprocessing";
	public static final String RUN = "Run";
	public static final String GLOBAL = "Global";
	public static final String NUMBER = "number";
	public static final String NAME = "name";
	public static final String N_TYPES = "nTypes";
	public static final String N_VALUES = "nValues";
	public static final String N_DELETED = "nDeleted";
	public static final String COUNT = "count";
	public static final String N_DISCARDED = "nDiscarded";
	public static final String N_ISOLATED = "nIsolated";
	public static final String N_FIXED = "nFixed";
	public static final String N_SYMBOLIC = "nSymbolic";
	public static final String N_AUXILIARY = "nAuxiliary";
	public static final String DEGREES = "degrees";

	public static final String N_REMOVED1 = "nRemoved1";
	public static final String N_CONVERTED = "nConverted";
	public static final String N_SPECIFIC = "nSpecific";
	public static final String N_MERGED = "nMerged";
	public static final String N_ADDED = "nAdded";
	public static final String N_GENERATORS = "nGenerators";
	public static final String N_CLIQUES = "nCliques";
	public static final String ARITIES = "arities";
	public static final String DISTRIBUTION = "distribution";
	public static final String SIZES = "sizes";
	public static final String TYPES = "types";
	public static final String TABLES = "tables";
	public static final String N_TUPLES = "nTuples";

	public static final String N_EXT_STRUCTURES = "nExtStructures";
	public static final String N_INT_STRUCTURES = "nIntStructures";
	public static final String N_CFT_STRUCTURES = "nCftStructures";
	public static final String SHARED = "shared";
	public static final String UNBUILT = "unbuilt";
	public static final String SHARED_BITS = "sharedBits";

	public static final String WAY = "way";
	public static final String TYPE = "type";
	public static final String BOUNDS = "bounds";

	public static final String DEPTHS = "dpts";
	public static final String N_EFFECTIVE = "effs";
	public static final String N_WRONG = "wrgs";
	public static final String N_DECISIONS = "decs";
	public static final String N_BACKTRACKS = "backs";
	public static final String N_FAILED = "fails";
	public static final String N_NOGOODS = "ngds";
	public static final String REVISIONS = "revisions";
	public static final String GUARANTEED_GAC = "guaranteedGAC";
	public static final String N_REMOVED_TUPLES = "nRemovedTuples";
	public static final String N_ADDED_CTRS = "nAddedCtrs";
	public static final String REMOVED_BY_AC = "removedByAC";
	public static final String UNSAT = "unsat";

	public static final String N_SINGLETON_TESTS = "nSingTests";
	public static final String N_EFFECTIVE_SINGLETON_TESTS = "nEffSingTests";
	public static final String N_FOUND_SINGLETONS = "nSingFound";
	public static final String N_BUILT_BRANCHES = "nBranches";
	public static final String SUM_BRANCH_SIZES = "sumBranches";

	public static final String INSTANTIATION = "instantiation";
	public static final String SELECTION = "selection";
	public static final String PRIORITY = "priority";
	public static final String N_STRICT_PRIORITY = "nStrictPriority";

	public static final String SOLS = "sols";
	public static final String SOL1_CPU = "sol1Cpu";
	public static final String BOUND = "bound";
	public static final String BOUND_WCK = "boundWck";
	public static final String BOUND_CPU = "boundCpu";

	public static final String WCK = "wck";
	public static final String CPU = "cpu";
	public static final String MEM = "mem";

	public static final String MAP_SIZE = "mapSize";
	public static final String N_INFERENCES = "nInferences";
	public static final String N_TOO_LARGE_KEYS = "nTooLargeKeys";
	public static final String N_SELIMINABLES = "nSEliminables";
	public static final String N_RELIMINABLES = "nREliminables";
	public static final String N_DELIMINABLES = "nDEliminables";
	public static final String N_IELIMINABLES = "nIEliminables";
	public static final String N_PELIMINABLES = "nPEliminables";

	public static final String STOP = "Stop";

	public static final String N_NODES = "nNodes";
	public static final String COMMENT_PREFIX = "  ";

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static String getOutputFileNamePrefixFrom(String fullInstanceName, String fullConfigurationName) {
		return Kit.getRawInstanceName(fullInstanceName) + (fullConfigurationName != null ? "_" + Kit.getXMLBaseNameOf(fullConfigurationName) + "_" : "");
	}

	/**********************************************************************************************
	 * Fields and methods
	 *********************************************************************************************/

	/**
	 * The head (main object for resolution) to which the object is attached
	 */
	private final Head head;

	private Features features;

	private Statistics stats;

	/**
	 * The XMl document built when solving a problem instance, if in campaign mode
	 */
	private Document document;

	private Element root;

	private Element resolElt;

	private Element solverElt;

	/**
	 * The filename of the generated XML file (with details about the solving process), if in campaign mode
	 */
	private String outputFileName;

	public Output(Head head, String configFileName) {
		this.head = head;
		if (head.control.xml.dirForCampaign.length() > 0) {
			this.document = Kit.createNewDocument();
			this.root = document.createElement(TypeOutput.RESOLUTIONS.toString());
			root.setAttribute(CONFIGURATION_FILE_NAME, configFileName);
			document.appendChild(root);
			document.normalize();
		}
	}

	public String outputFileNameFrom(String fullInstanceName, String configurationFileName) {
		String hostName = "unknown";
		try {
			hostName = InetAddress.getLocalHost().getCanonicalHostName();
		} catch (UnknownHostException e) {
			e.printStackTrace();
		}
		return getOutputFileNamePrefixFrom(fullInstanceName, configurationFileName) + hostName + "_" + Kit.date() + ".xml";
	}

	public Element record(TypeOutput output, Collection<Entry<String, Object>> entries, Element parent) {
		if (document == null)
			return null;
		Element child = Utilities.element(document, output.toString(), entries);
		if (parent == null)
			root.appendChild(child);
		else
			parent.appendChild(child);
		return child;
	}

	public void beforeData() { // not a method from an observer
		this.resolElt = record(TypeOutput.RESOLUTION, null, root);
	}

	public void afterData() { // not a method from an observer
		InformationBloc info = instanceInfo(head.instanceNumber);
		save(head.instanceStopwatch.wckTime());
		Kit.log.config(COMMENT_PREFIX + Kit.preprint("Instance ", Kit.BLUE) + head.problem.name() + "\n");
		record(TypeOutput.INSTANCE, info.entries(), resolElt);
	}

	@Override
	public void afterProblemConstruction() {
		Kit.control(head.problem.variables.length > 0, () -> "No variable in your model");
		this.features = head.problem.features;
		InformationBloc dinfo = domainsInfo();
		InformationBloc vinfo = variablesInfo();
		InformationBloc cinfo = constraintsInfo();
		InformationBloc oinfo = head.problem.optimizer != null ? objectiveInfo() : null;
		record(TypeOutput.DOMAINS, dinfo.entries(), resolElt);
		record(TypeOutput.VARIABLES, vinfo.entries(), resolElt);
		record(TypeOutput.CONSTRAINTS, cinfo.entries(), resolElt);
		if (oinfo != null)
			record(TypeOutput.OBJECTIVE, oinfo.entries(), resolElt);
		Kit.log.config("\n" + dinfo.toString() + "\n" + vinfo.toString() + "\n" + cinfo.toString() + (oinfo == null ? "" : "\n" + oinfo.toString()));
	}

	@Override
	public void afterSolverConstruction() {
		this.stats = head.solver.stats;
		InformationBloc info = solverInfo();
		this.solverElt = record(TypeOutput.SOLVER, info.entries(), resolElt);
		Kit.log.config("\n" + info.toString());
	}

	@Override
	public final void afterPreprocessing() {
		InformationBloc info = preproInfo();
		record(TypeOutput.PREPROCESSING, info.entries(), solverElt);
		Kit.log.config("\n" + info.toString() + "\n");
	}

	@Override
	public final void afterRun() {
		InformationBloc info = runInfo();
		record(TypeOutput.RUN, info.entries(), solverElt);
		Kit.log.config(info.toString());
	}

	@Override
	public final void afterSolving() {
		InformationBloc info = globalInfo();
		record(TypeOutput.GLOBAL, info.entries(), solverElt);
		Kit.log.config("\n" + info.toString());
	}

	public String save(long totalWck) {
		if (document == null)
			return null;
		root.setAttribute(TOTAL_WCK_TIME, totalWck + "");
		String dirName = head.control.xml.dirForCampaign + File.separator + RESULTS_DIRECTORY;
		File file = new File(dirName);
		if (!file.exists())
			file.mkdirs();
		// we record the name of the output file, the first time a saving operation is execute
		this.outputFileName = this.outputFileName != null ? this.outputFileName : outputFileNameFrom(head.problem.name(), head.control.settingsFilename);
		return Utilities.save(document, dirName + File.separator + outputFileName);
	}

	/**********************************************************************************************
	 * Section about blocks of information, of the form of pairs (key-value), that can be displayed
	 *********************************************************************************************/

	public final static class InformationBloc {

		public static final String SEPARATOR = "separator";

		private String name;

		private List<Entry<String, Object>> list = new ArrayList<>();

		public InformationBloc(String name) {
			this.name = name;
		}

		public InformationBloc put(String key, Object value, boolean condition) {
			if (value instanceof String && ((String) value).length() == 0)
				return this;
			if (value instanceof Integer && ((Integer) value) == 0 && !key.contentEquals("run"))
				return this;
			if (value instanceof Long && ((Long) value) == 0)
				return this;
			// if (value instanceof Number && ((Number) value).doubleValue() == 0)
			// return this;
			if (condition)
				list.add(new SimpleEntry<>(key, value));
			return this;
		}

		public InformationBloc put(String key, Object value) {
			return put(key, value, true);
		}

		public InformationBloc separator(boolean condition) {
			return put(SEPARATOR, null, condition);
		}

		public InformationBloc separator() {
			return put(SEPARATOR, null, true);
		}

		public List<Entry<String, Object>> entries() {
			return list.stream().filter(e -> e.getKey() != SEPARATOR).collect(Collectors.toCollection(ArrayList::new));
		}

		@Override
		public String toString() {
			String s = (name.equals(RUN) ? "" : Output.COMMENT_PREFIX + Kit.preprint(name, Kit.BLUE) + "\n") + Output.COMMENT_PREFIX + Output.COMMENT_PREFIX;
			boolean sep = true;
			for (int i = 0; i < list.size(); i++) {
				Entry<String, Object> e = list.get(i);
				if (e.getKey() == SEPARATOR) {
					s += "\n" + Output.COMMENT_PREFIX + Output.COMMENT_PREFIX;
					sep = true;
				} else {
					if (!sep)
						s += "  ";
					s += (e.getKey() + "=" + e.getValue());
					sep = false;
				}
			}
			return s;
		}
	}

	private InformationBloc instanceInfo(int instanceNumber) {
		SettingVars settings = head.control.variables;
		InformationBloc m = new InformationBloc(INSTANCE);
		m.put(NAME, head.problem.name());
		m.put(NUMBER, instanceNumber, Input.nInstancesToSolve > 1);
		m.separator(settings.selectedVars.length > 0 || settings.instantiatedVars.length > 0 || settings.priorityVars.length > 0);
		m.put(SELECTION, Stream.of(settings.selectedVars).map(o -> o.toString()).collect(joining(",")));
		m.put(INSTANTIATION, IntStream.range(0, settings.instantiatedVars.length)
				.mapToObj(i -> settings.instantiatedVars[i] + "=" + settings.instantiatedVals[i]).collect(joining(",")));
		m.put(PRIORITY, Stream.of(settings.priorityVars).map(o -> o.toString()).collect(joining(",")));
		m.put(N_STRICT_PRIORITY, settings.nStrictPriorityVars);
		return m;
	}

	private InformationBloc domainsInfo() {
		InformationBloc m = new InformationBloc(DOMAINS);
		m.put(N_TYPES, features.nDomTypes());
		m.put(N_VALUES, Variable.nValidValuesFor(head.problem.variables));
		Kit.control(features.nValuesRemovedAtConstructionTime == head.problem.nValueRemovals);
		m.put(N_DELETED, head.problem.nValueRemovals);
		m.put(SIZES, features.domSizes);
		return m;
	}

	private InformationBloc variablesInfo() {
		InformationBloc m = new InformationBloc(VARIABLES);
		m.put(COUNT, head.problem.variables.length);
		m.put(N_DISCARDED, features.collecting.discardedVars.size());
		m.put(N_ISOLATED, features.nIsolatedVars);
		m.put(N_FIXED, features.nFixedVars);
		m.put(N_SYMBOLIC, features.nSymbolicVars);
		m.put(N_AUXILIARY, head.problem.nAuxVariables);
		m.put(DEGREES, features.varDegrees);
		return m;
	}

	private InformationBloc constraintsInfo() {
		InformationBloc m = new InformationBloc(CONSTRAINTS);
		m.put(COUNT, head.problem.constraints.length);
		m.put(N_REMOVED1, features.nRemovedUnaryCtrs);
		m.put(N_CONVERTED, features.nConvertedConstraints);
		m.put(N_SPECIFIC, features.nSpecificCtrs);
		m.put(N_MERGED, features.nMergedCtrs);
		m.put(N_DISCARDED, features.nDiscardedCtrs);
		m.put(N_ADDED, features.nAddedCtrs);
		m.put(N_GENERATORS, features.nGenerators); // for symmetry-breaking constraints
		m.put(N_CLIQUES, features.nCliques); // for redundant AllDifferent constraints
		m.put(ARITIES, features.ctrArities);
		m.separator();
		m.put(DISTRIBUTION, features.ctrTypes);
		m.separator(features.tableSizes.size() > 0);
		m.put(TABLES, features.tableSizes.toString());
		m.put(N_TUPLES, features.tableSizes.repartition.entrySet().stream().mapToLong(e -> e.getValue() * (Integer) e.getKey()).sum());
		int nExtStructures = 0, nSharedExtStructures = 0, nIntStructures = 0, nSharedintStructures = 0, nCftStructures = 0, nSharedCftStructures = 0;
		for (Constraint c : head.problem.constraints) {
			if (c instanceof Extension)
				if (c.extStructure().firstRegisteredCtr() == c)
					nExtStructures++;
				else
					nSharedExtStructures++;
			if (c instanceof Intension)
				if (c.intStructure().firstRegisteredCtr() == c)
					nIntStructures++;
				else
					nSharedintStructures++;
			if (c.conflictsStructure != null)
				if (c.conflictsStructure.firstRegisteredCtr() == c)
					nCftStructures++;
				else
					nSharedCftStructures++;
		}
		m.separator(nExtStructures > 0 || nIntStructures > 0 || nCftStructures > 0 || features.nSharedBitVectors > 0);
		m.put(N_EXT_STRUCTURES, "(" + nExtStructures + ",shared:" + nSharedExtStructures + ")", nExtStructures > 0);
		m.put(N_INT_STRUCTURES, "(" + nIntStructures + ",shared:" + nSharedintStructures + ")", nIntStructures > 0);
		int unbuilt = head.problem.constraints.length - nCftStructures - nSharedCftStructures;
		m.put(N_CFT_STRUCTURES, "(" + nCftStructures + ",shared:" + nSharedCftStructures + ",unbuilt:" + unbuilt + ")", nCftStructures > 0);
		m.put(SHARED_BITS, features.nSharedBitVectors);
		m.separator();
		m.put(WCK, head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	private InformationBloc objectiveInfo() {
		Optimizer optimizer = head.problem.optimizer;
		if (optimizer.ctr == null)
			return null;
		Kit.control(optimizer.ctr != null);
		InformationBloc m = new InformationBloc(OBJECTIVE);
		m.put(WAY, (optimizer.minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName());
		m.put(TYPE, optimizer.ctr.getClass().getSimpleName());
		m.put(BOUNDS, (optimizer.clb.limit() + ".." + optimizer.cub.limit()));
		return m;
	}

	private final InformationBloc solverInfo() {
		InformationBloc m = new InformationBloc(SOLVER);
		m.put(GUARANTEED_GAC, head.solver.propagation.getClass() == GAC.class ? ((GAC) head.solver.propagation).guaranteed : "");
		m.separator();
		m.put(WCK, head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	private final InformationBloc preproInfo() {
		InformationBloc m = new InformationBloc(PREPROCESSING);
		m.put(N_EFFECTIVE, head.problem.features.nEffectiveFilterings);
		m.put(REVISIONS, "(" + stats.nRevisions() + ",useless=" + stats.nUselessRevisions() + ")", stats.nRevisions() > 0);
		m.put(N_VALUES, Variable.nValidValuesFor(head.problem.variables));
		Propagation propagation = head.solver.propagation;
		m.put(REMOVED_BY_AC, propagation instanceof GAC ? ((GAC) (propagation)).nPreproValueRemovals : 0);
		// m.put("nTotalRemovedValues", nPreproRemovedValues);
		m.put(UNSAT, head.solver.stopping == EStopping.FULL_EXPLORATION);
		m.separator(stats.nPreproRemovedTuples > 0 || stats.nPreproAddedNogoods > 0 || stats.nPreproAddedCtrs > 0);
		m.put(N_REMOVED_TUPLES, stats.nPreproRemovedTuples);
		m.put(N_NOGOODS, stats.nPreproAddedNogoods);
		m.put(N_ADDED_CTRS, stats.nPreproAddedCtrs);
		m.separator(propagation.nSingletonTests > 0);
		m.put(N_SINGLETON_TESTS, propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, propagation.nEffectiveSingletonTests);
		m.put(N_FOUND_SINGLETONS, propagation instanceof SAC ? ((SAC) (propagation)).nFoundSingletons : 0);
		m.put(N_BUILT_BRANCHES, propagation instanceof SACGreedy ? ((SACGreedy) (propagation)).nBranchesBuilt : 0);
		m.put(SUM_BRANCH_SIZES, propagation instanceof SACGreedy ? ((SACGreedy) (propagation)).sumBranchSizes : 0);
		m.separator();
		m.put(SOLS, head.solver.solutions.found);
		m.put(SOL1_CPU, stats.firstSolCpu / 1000.0, head.solver.solutions.found > 0);
		m.put(WCK, stats.preproWck / 1000.0);
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	private InformationBloc runInfo() {
		InformationBloc m = new InformationBloc(RUN);
		m.put("run", head.solver.restarter.numRun);
		m.put(DEPTHS, head.solver.minDepth + ".." + head.solver.maxDepth);
		m.put(N_EFFECTIVE, features.nEffectiveFilterings);
		m.put(N_WRONG, stats.nWrongDecisions);
		if (Kit.memory() > 10000000000L)
			m.put(MEM, Kit.memoryInMb());
		m.put(WCK, stats.stopwatch.wckTimeInSeconds());
		m.put(N_NOGOODS, head.solver.nogoodRecorder != null ? head.solver.nogoodRecorder.nNogoods : 0);
		if (head.solver.solutions.found > 0) {
			if (head.problem.settings.framework == TypeFramework.CSP)
				m.put(SOLS, head.solver.solutions.found);
			else {
				if (head.problem.optimizer.minBound == 0 || head.problem.optimizer.minBound == Long.MIN_VALUE)
					m.put(BOUND, stats.nformat.format(head.solver.solutions.bestBound));
				else
					m.put(BOUNDS, head.problem.optimizer.stringBounds());
			}
		}
		if (head.control.general.verbose <= 1)
			return m;
		m.separator();
		m.put(N_DECISIONS, stats.nDecisions);
		m.put(N_BACKTRACKS, stats.nBacktracks);
		m.put(N_FAILED, stats.nFailedAssignments);
		m.put(REVISIONS, "(" + stats.nRevisions() + ",useless=" + stats.nUselessRevisions() + ")", stats.nRevisions() > 0);
		m.put(N_SINGLETON_TESTS, head.solver.propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, head.solver.propagation.nEffectiveSingletonTests);
		if (Kit.memory() > 10000000000L)
			m.put(MEM, Kit.memoryInMb());
		m.separator();
		IpsRecorder ipsRecorder = head.solver.ipsRecorder;
		if (ipsRecorder instanceof IpsRecorderForEquivalence && !ipsRecorder.stopped) {
			IpsRecorderForEquivalence recorder = (IpsRecorderForEquivalence) ipsRecorder;
			m.put(MAP_SIZE, recorder.getMapSize());
			m.put(N_INFERENCES, recorder.nInferences);
			m.put(N_TOO_LARGE_KEYS, recorder.nTooLargeKeys);
		}
		if (ipsRecorder != null) {
			ReductionOperator ro = ipsRecorder.reductionOperator;
			m.put(N_SELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbSEliminableVariables()));
			m.put(N_RELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbREliminableVariables()));
			m.put(N_IELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbIEliminableVariables()));
			m.put(N_DELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbDEliminableVariables()));
			m.put(N_PELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbPEliminableVariables()));
			m.separator();
		}
		return m;
	}

	private InformationBloc globalInfo() {
		InformationBloc m = new InformationBloc(GLOBAL);
		m.put(N_EFFECTIVE, head.problem.features.nEffectiveFilterings);
		m.put(REVISIONS, "(" + stats.nRevisions() + ",useless=" + stats.nUselessRevisions() + ")", stats.nRevisions() > 0);
		m.put(N_SINGLETON_TESTS, head.solver.propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, head.solver.propagation.nEffectiveSingletonTests);
		m.put(N_NOGOODS, head.solver.nogoodRecorder != null ? head.solver.nogoodRecorder.nNogoods : 0);
		m.separator();
		m.put(STOP, head.solver.stopping == null ? "no" : head.solver.stopping.toString());
		m.put(N_WRONG, stats.nWrongDecisions);
		if (head.solver.solutions.found > 0) {
			if (head.problem.settings.framework != TypeFramework.CSP) {
				m.put(BOUND, head.solver.solutions.bestBound);
				m.put(BOUND_WCK, stats.lastSolWck / 1000.0);
				m.put(BOUND_CPU, stats.lastSolCpu / 1000.0);
			}
			m.put(SOLS, head.solver.solutions.found);
			m.put(SOL1_CPU, stats.firstSolCpu / 1000.0);
		}
		m.separator();
		m.put(WCK, head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

}
