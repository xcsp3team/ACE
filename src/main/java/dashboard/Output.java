/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package dashboard;

import static utility.Kit.control;
import static utility.Kit.log;

//import java.awt.Color;
import java.io.File;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.text.NumberFormat;
import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
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
import constraints.ConstraintExtension;
import constraints.ConstraintIntension;
import dashboard.Control.OptionsVariables;
import heuristics.HeuristicValues;
import heuristics.HeuristicValuesDirect;
import heuristics.HeuristicVariablesDynamic.RunRobin;
import interfaces.Observers.ObserverOnConstruction;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Observers.ObserverOnSolving;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.SpecificPropagator;
import learning.IpsExtractor;
import learning.IpsReasoner;
import learning.IpsReasonerEquivalence;
import main.Head;
import optimization.Optimizer;
import problem.Features;
import problem.Problem;
import problem.XCSP3;
import propagation.AC;
import propagation.Propagation;
import propagation.SAC.SACGreedy;
import solver.Solver.Stopping;
import solver.Statistics;
import utility.Kit;
import utility.Kit.Color;
import variables.Variable;

/**
 * The role of this class is to output some data/information concerning the solving process of problem instances. These data are collected by means of an XML
 * document that may be saved. A part of the data are also directly displayed on the standard output.
 * 
 * @author Christophe Lecoutre
 */
public class Output implements ObserverOnConstruction, ObserverOnSolving, ObserverOnRuns {

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		control(n > 0, () -> "No variable in your model");
		this.features = head.problem.features;
		InformationBloc dinfo = domainsInfo();
		InformationBloc vinfo = variablesInfo();
		InformationBloc cinfo = constraintsInfo();
		InformationBloc oinfo = head.problem.optimizer != null ? objectiveInfo() : null;
		record(DOMAINS, dinfo, resolution);
		record(VARIABLES, vinfo, resolution);
		record(CONSTRAINTS, cinfo, resolution);
		if (oinfo != null)
			record(OBJECTIVE, oinfo, resolution);
		log.config("\n" + dinfo + "\n" + vinfo + "\n" + cinfo + (oinfo == null ? "" : "\n" + oinfo));
	}

	@Override
	public void afterSolverConstruction() {
		this.stats = head.solver.stats;
		InformationBloc info = solverInfo();
		this.solver = record(SOLVER, info, resolution);
		log.config("\n" + info);
	}

	@Override
	public final void afterPreprocessing() {
		InformationBloc info = preproInfo();
		record(PREPROCESSING, info, solver);
		log.config("\n" + info + "\n");
		if (head.control.general.removedAfterProcessing) {
			System.out.println("  " + Color.BLUE.coloring("Domain State") + " (removals after preprocessing)");
			for (Variable x : head.problem.variables)
				if (x.dom.nRemoved() > 0 && x.dom.lastRemoved() != -1)
					System.out.println("    " + x + " : " + x.dom.stringOfRemovedValues());
			System.out.println();
		}
		log.config(COMMENT_PREFIX + Color.BLUE.coloring("search"));
	}

	@Override
	public void beforeSearch() {
		wckBeforeSearch = System.currentTimeMillis();
	}

	@Override
	public final void afterRun() {
		InformationBloc info = runInfo();
		record(RUN, info, solver);
		log.config(info.toString());
	}

	@Override
	public final void afterSolving() {
		InformationBloc info = globalInfo();
		record(GLOBAL, info, solver);
		log.config("\n" + info);

		if (head.solver.solutions.store != null) {
			try (PrintWriter out = new PrintWriter("Solutions-" + head.problem.name() + ".json")) {
				out.println("{");
				out.println("\"scope\": [" + Stream.of(head.problem.variables).map(x -> "\"" + x.id + "\"").collect(Collectors.joining(", ")) + "], ");
				out.print("\"table\": [");
				int cnt = 0;
				for (Object t : head.solver.solutions.store) {
					cnt++;
					// out.print(t instanceof int[] ? Kit.compactValues((int[]) t, 3) : t);
					// out.print(t instanceof int[] ? Arrays.toString((int[]) t) : t);
					out.print(t instanceof int[] ? "[" + IntStream.of((int[]) t).mapToObj(v -> v + "").collect(Collectors.joining(",")) + "]" : t);
					if (cnt < head.solver.solutions.store.size())
						out.println(", ");
				}
				out.println("]");
				out.println("}");
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

	}

	/**********************************************************************************************
	 * Static members
	 *********************************************************************************************/

	/**
	 * An object for formatting numbers when outputting
	 */
	public static NumberFormat numberFormat = NumberFormat.getInstance();

	/**
	 * An object for formatting decimal numbers when outputting
	 */
	public static DecimalFormat decimalFormat = new DecimalFormat("###.##", new DecimalFormatSymbols(Locale.ENGLISH));

	public static final String RESOLUTIONS = "resolutions";
	public static final String RESOLUTION = "resolution";
	public static final String INSTANCE = "instance";
	public static final String DOMAINS = "domains";
	public static final String VARIABLES = "variables";
	public static final String CONSTRAINTS = "constraints";
	public static final String OBJECTIVE = "objective";
	public static final String SOLVER = "solver";
	public static final String PREPROCESSING = "preprocessing";
	public static final String RUN = "run";
	public static final String GLOBAL = "global";

	public static final String NUMBER = "number";
	public static final String NAME = "name";
	public static final String ARGS = "args";
	public static final String N_TYPES = "types";
	public static final String N_VALUES = "values";
	public static final String N_DELETED = "deleted";
	public static final String N_SINGLETONS = "singletons";
	public static final String COUNT = "count";
	public static final String N_OMITTED = "omitted";
	public static final String N_DISCARDED = "discarded";
	public static final String N_ISOLATED = "isolated";
	public static final String N_FIXED = "fixed";
	public static final String N_SYMBOLIC = "symbolic";
	public static final String N_AUXILIARY = "auxiliary";
	public static final String DEGREES = "degrees";

	public static final String N_ARRAYS = "arrays";
	public static final String PRIORITY_ARRAYS = "priorityArrays";
	public static final String N_REMOVED1 = "removed1";
	public static final String N_CONVERTED = "converted";
	public static final String N_SPECIFIC = "specific";
	public static final String N_MERGED = "merged";
	public static final String N_ADDED = "added";
	public static final String N_GROUPS = "groups";
	public static final String IGNORED_GROUPS = "ignoredGroups";
	public static final String N_GENERATORS = "generators";
	public static final String N_CLIQUES = "cliques";
	public static final String ARITIES = "arities";
	public static final String DISTRIBUTION = "distribution";
	public static final String SIZES = "sizes";
	public static final String TYPES = "types";
	public static final String TABLES = "tables";
	public static final String N_TUPLES = "tuples";

	public static final String N_EXT_STRUCTURES = "extStructures";
	public static final String N_INT_STRUCTURES = "intStructures";
	public static final String N_CFT_STRUCTURES = "cftStructures";
	public static final String SHARED = "shared";
	public static final String UNBUILT = "unbuilt";
	public static final String SHARED_BITS = "sharedBits";

	public static final String WAY = "way";
	public static final String TYPE = "type";
	public static final String BOUNDS = "bounds";

	public static final String DEPTHS = "dpts";
	public static final String N_EFFECTIVE = "effs";
	public static final String N_ENTAILED = "entailed";
	public static final String N_WRONG = "wrgs";
	public static final String N_DECISIONS = "decs";
	public static final String N_BACKTRACKS = "backs";
	public static final String N_FAILED = "fails";
	public static final String N_NOGOODS = "ngds";
	public static final String REVISIONS = "revisions";
	public static final String GUARANTEED_AC = "guaranteedAC";
	public static final String N_REMOVED_TUPLES = "removedTuples";
	public static final String N_ADDED_CTRS = "addedCtrs";
	public static final String REMOVED_BY_AC = "removedByAC";
	public static final String UNSAT = "unsat";

	public static final String N_SINGLETON_TESTS = "singTests";
	public static final String N_EFFECTIVE_SINGLETON_TESTS = "effSingTests";
	public static final String N_BRANCHES = "branches";
	public static final String SUM_BRANCHES = "sumBranches";

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
	public static final String STOP = "stop";
	public static final String N_NODES = "nodes";

	public static final String MAP_SIZE = "mapSize";
	public static final String N_INFERENCES = "inferences";
	public static final String N_TOO_LARGE_KEYS = "nTooLargeKeys";
	public static final String N_SELIMINABLES = "nSEliminables";
	public static final String N_RELIMINABLES = "nREliminables";
	public static final String N_DELIMINABLES = "nDEliminables";
	public static final String N_IELIMINABLES = "nIEliminables";
	public static final String N_PELIMINABLES = "nPEliminables";

	public static final String RESULTS_DIRECTORY = "results";
	public static final String SETTINGS_DIRECTORY = "configurations";
	public static final String CONTEXT_DIRECTORY = "context";
	public static final String MULTITHREAD_RESULTS = "multithreadResults";
	public static final String CONFIGURATION_FILE_NAME = "configurationFileName";
	public static final String TOTAL_WCK_TIME = "totalWckTime";

	public static final String COMMENT_PREFIX = "  ";

	public static String getOutputFileNamePrefixFrom(String fullInstanceName, String fullConfigurationName) {
		String s = fullInstanceName;
		int first = s.lastIndexOf(File.separator) != -1 ? s.lastIndexOf(File.separator) + 1 : 0;
		int last = s.lastIndexOf(".") != -1 ? s.lastIndexOf(".") : s.length();
		s = first > last ? s.substring(first) : s.substring(first, last);
		return s + (fullConfigurationName != null ? "_" + Kit.getXMLBaseNameOf(fullConfigurationName) + "_" : "");
	}

	/**********************************************************************************************
	 * Fields and methods
	 *********************************************************************************************/

	/**
	 * The head (main object for resolution) to which the object is attached
	 */
	private final Head head;

	/**
	 * The features of the problem (redundant field)
	 */
	private Features features;

	/**
	 * The statistics of the solver (redundant field)
	 */
	private Statistics stats;

	/**
	 * The XMl document built when solving a problem instance, if in campaign mode
	 */
	private Document document;

	private Element root;

	private Element resolution;

	private Element solver;

	/**
	 * The filename of the generated XML file (with details about the solving process), if in campaign mode
	 */
	private String outputFileName;

	public long wckBeforeSearch;

	/**
	 * Builds an object Output for the specified head
	 * 
	 * @param head
	 *            the head to which the object is attached
	 * @param configurationFilename
	 *            the name of the file with option settings
	 */
	public Output(Head head, String configurationFilename) {
		this.head = head;
		if (head.control.general.campaignDir.length() > 0) {
			this.document = Kit.createNewDocument();
			this.root = document.createElement(RESOLUTIONS);
			root.setAttribute(CONFIGURATION_FILE_NAME, configurationFilename);
			document.appendChild(root);
			document.normalize();
		}
	}

	public String outputFileNameFrom(String fullInstanceName, String controlFilename) {
		String hostName = "unknown";
		try {
			hostName = InetAddress.getLocalHost().getCanonicalHostName();
		} catch (UnknownHostException e) {
			e.printStackTrace();
		}
		return getOutputFileNamePrefixFrom(fullInstanceName, controlFilename) + hostName + "_" + Kit.date() + ".xml";
	}

	/**
	 * Builds and records a new element to the document (if not null). The element is created from the specified tag, entries for attributes and the parent node
	 * 
	 * @param tag
	 *            the tag for the element to be created
	 * @param entries
	 *            the entries representing attributes
	 * @param parent
	 *            the parent of the new created element, or root if null
	 * @return a new created element, or null
	 */
	public Element record(String tag, Stream<Entry<String, Object>> entries, Element parent) {
		if (document == null)
			return null;
		Element child = Utilities.element(document, tag, entries);
		if (parent == null)
			root.appendChild(child);
		else
			parent.appendChild(child);
		return child;
	}

	private Element record(String tag, InformationBloc bloc, Element parent) {
		return record(tag, bloc.filtered_entries(), parent);
	}

	/**
	 * Method called before loading/setting data. REMARK: this is not a method from an observer.
	 */
	public void beforeData() {
		this.resolution = record(RESOLUTION, (Stream<Entry<String, Object>>) null, root);
	}

	/**
	 * Method called after loading/setting data. REMARK: this is not a method from an observer.
	 */
	public void afterData() {
		InformationBloc info = instanceInfo(head.instanceIndex);
		save(head.instanceStopwatch.wckTime());
		// log.config(COMMENT_PREFIX + Color.BLUE.coloring("Instance ") + head.problem.name() + "\n");
		log.config(info + "\n");
		record(INSTANCE, info.filtered_entries(), resolution);
	}

	/**
	 * Saves the XMl document, if in campaign mode
	 * 
	 * @param totalWck
	 *            the total elapsed wall clock time
	 * @return the filename of the saved XMl document, or null
	 */
	public String save(long totalWck) {
		if (document == null)
			return null;
		root.setAttribute(TOTAL_WCK_TIME, totalWck + "");
		String dirName = head.control.general.campaignDir + File.separator + RESULTS_DIRECTORY;
		File file = new File(dirName);
		if (!file.exists())
			file.mkdirs();
		// we record the name of the output file, the first time a saving operation is executed
		this.outputFileName = this.outputFileName != null ? this.outputFileName
				: outputFileNameFrom(head.problem.name(), head.control.userSettings.controlFilename);
		return Utilities.save(document, dirName + File.separator + outputFileName);
	}

	/**********************************************************************************************
	 * Section about blocks of information, of the form of pairs (key-value), that can be displayed
	 *********************************************************************************************/

	private final static class InformationBloc {

		private static final String SEPARATOR = "separator";

		/**
		 * Name of the information bloc
		 */
		private String name;

		/**
		 * List of entries (i.e., pairs keys-values) in the information bloc
		 */
		private List<Entry<String, Object>> entries = new ArrayList<>();

		private InformationBloc(String name) {
			this.name = name;
		}

		private InformationBloc put(String key, Object value, boolean condition) {
			if (value instanceof String && (value.equals("") || value.equals("0")))
				return this; // not recorded because empty string
			if (value instanceof Integer && ((Integer) value) == 0 && !key.contentEquals("run"))
				return this; // not recorded because 0, except if the key is 'run'
			if (value instanceof Long && ((Long) value) == 0)
				return this; // not recorded because 0
			if (condition)
				entries.add(new SimpleEntry<>(key, value));
			return this;
		}

		private InformationBloc put(String key, Object value) {
			return put(key, value instanceof Number ? numberFormat.format(value) : value, true);
		}

		private InformationBloc separator(boolean condition) {
			return put(SEPARATOR, null, condition);
		}

		private InformationBloc separator() {
			return put(SEPARATOR, null, true);
		}

		private Stream<Entry<String, Object>> filtered_entries() {
			return entries.stream().filter(e -> e.getKey() != SEPARATOR);
		}

		@Override
		public String toString() {
			String sep_char = ":";
			StringBuilder sb = new StringBuilder(COMMENT_PREFIX).append(COMMENT_PREFIX);
			boolean sep = true;
			int l = sb.length();
			for (Entry<String, Object> entry : entries) {
				String key = entry.getKey();
				if (key == SEPARATOR) {
					if (l != sb.length())
						sb.append("\n").append(COMMENT_PREFIX).append(COMMENT_PREFIX);
					sep = true;
				} else {
					if (!sep)
						sb.append("  ");
					sb.append(key).append(key.equals(RUN) ? "" : sep_char).append(entry.getValue());
					sep = false;
				}
			}
			// The special character in preprint cannot be put in StringBuilder
			return (name.equals(RUN) ? "" : COMMENT_PREFIX + Color.BLUE.coloring(name) + (entries.size() > 0 ? "\n" : "")) + sb.toString();
		}
	}

	private InformationBloc instanceInfo(int instanceNumber) {
		OptionsVariables options = head.control.variables;
		InformationBloc m = new InformationBloc(INSTANCE);
		m.put(NAME, head.problem.name());
		m.put(NUMBER, instanceNumber, Input.nInstancesToSolve > 1);
		m.separator();
		m.put(ARGS, Stream.of(Input.args).collect(Collectors.joining(" ")));

		m.separator(options.selection.length() > 0 || options.instantiation.length() > 0 || options.priority1.length() > 0 || options.priority2.length() > 0);
		m.put(SELECTION, options.selection);
		m.put(INSTANTIATION, options.instantiation);
		m.put(PRIORITY, options.priority1.length() > 0 || options.priority2.length() > 0 ? options.priority1 + " - " + options.priority2 : "");
		return m;
	}

	private InformationBloc domainsInfo() {
		InformationBloc m = new InformationBloc(DOMAINS);
		m.put(N_TYPES, features.nDomTypes());
		m.put(N_VALUES, Variable.nValidValuesFor(head.problem.variables));
		control(features.nValuesRemovedAtConstructionTime == head.problem.nValueRemovals);
		m.put(N_DELETED, head.problem.nValueRemovals);
		m.put(SIZES, features.domSizes);
		return m;
	}

	private InformationBloc variablesInfo() {
		InformationBloc m = new InformationBloc(VARIABLES);
		m.put(COUNT, head.problem.variables.length);
		m.put(N_OMITTED, features.nOmittedVars);
		m.put(N_DISCARDED, features.collecting.discardedVars.size());
		m.put(N_ISOLATED, features.nIsolatedVars);
		m.put(N_FIXED, features.nFixedVars);
		m.put(N_SYMBOLIC, features.nSymbolicVars);
		m.put(N_AUXILIARY, head.problem.nAuxVariables);
		m.put(N_ARRAYS, "["
				+ Stream.of(head.problem.varArrays).map(va -> va.id + ":" + (va.flatVars != null ? va.flatVars.length : "")).collect(Collectors.joining(","))
				+ (head.problem.auxiliaryVars.length == 0 ? "" : "," + Problem.AUXILIARY_VARIABLE_PREFIX + ":" + head.problem.auxiliaryVars.length) + "]");
		if (head.problem.priorityVars == head.problem.auxiliaryVars)
			m.put(PRIORITY_ARRAYS, Problem.AUXILIARY_VARIABLE_PREFIX);
		else
			m.put(PRIORITY_ARRAYS, "" + Stream.of(head.problem.priorityArrays).map(pa -> pa.id).collect(Collectors.joining(",")));
		m.put(DEGREES, features.varDegrees);
		return m;
	}

	private InformationBloc constraintsInfo() {
		InformationBloc m = new InformationBloc(CONSTRAINTS);
		m.put(COUNT, head.problem.constraints.length);
		m.put(N_REMOVED1, features.nRemovedUnaryCtrs);
		m.put(N_CONVERTED, features.nConvertedConstraints);
		m.put("nNogoods", features.collecting.nogoods.size());
		m.put("nGatheredNogoods", features.collecting.nCollectedNogoodsGathered);
		m.put(N_SPECIFIC, Stream.of(head.problem.constraints).filter(c -> c instanceof SpecificPropagator).count());
		m.put("backtrack", Stream.of(head.problem.constraints).filter(c -> c instanceof ObserverOnBacktracksSystematic).count());
		m.put(N_MERGED, features.nMergedCtrs);
		m.put(N_DISCARDED, features.nDiscardedCtrs);
		m.put(N_ADDED, features.nAddedCtrs);
		m.put("postponable", features.nPostponableConstraints);
		if (head.problem.api instanceof XCSP3)
			m.put(N_GROUPS, ((XCSP3) head.problem.api).nGroups);
		m.put(IGNORED_GROUPS, head.control.constraints.ignoreGroups);
		m.put(N_GENERATORS, features.nGenerators); // for symmetry-breaking constraints
		m.put(N_CLIQUES, features.nCliques); // for redundant AllDifferent constraints
		m.put(ARITIES, features.ctrArities);
		m.separator();
		if (features.ctrTypes1.size() > 0 || head.problem.optimizer != null) {
			if (features.ctrTypes1.size() > 0)
				m.put("unary", features.ctrTypes1);
			if (head.problem.optimizer != null)
				m.put("objective",
						"[" + head.problem.optimizer.clb.getClass().getSimpleName() + "," + head.problem.optimizer.cub.getClass().getSimpleName() + "]");
			m.separator();
		}
		m.put("non_unary", features.ctrTypes);
		m.separator(features.tableSizes.size() > 0);
		m.put(TABLES, features.tableSizes.toString());
		m.put(N_TUPLES, features.tableSizes.repartition.entrySet().stream().mapToLong(e -> e.getValue() * e.getKey()).sum());
		m.separator(features.mddSizes.size() > 0);
		m.put("mdds", features.mddSizes.toString());
		m.put("nodes", features.mddSizes.repartition.entrySet().stream().mapToLong(e -> e.getValue() * e.getKey()).sum());

		int nExtStructures = 0, nSharedExtStructures = 0, nIntStructures = 0, nSharedintStructures = 0, nCftStructures = 0, nSharedCftStructures = 0;
		for (Constraint c : head.problem.constraints) {
			if (c instanceof ConstraintExtension)
				if (c.extStructure().firstRegisteredCtr() == c)
					nExtStructures++;
				else
					nSharedExtStructures++;
			if (c instanceof ConstraintIntension)
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
		control(optimizer.ctr != null);
		InformationBloc m = new InformationBloc(OBJECTIVE);
		m.put(WAY, (optimizer.minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName());
		m.put(TYPE, optimizer.ctr.getClass().getSimpleName());
		m.put("arity", ((Constraint) optimizer.ctr).scp.length);
		m.put(BOUNDS, (numberFormat.format(optimizer.clb.limit()) + ".." + numberFormat.format(optimizer.cub.limit())));
		return m;
	}

	private InformationBloc solverInfo() {
		InformationBloc m = new InformationBloc(SOLVER);
		m.put(GUARANTEED_AC, head.solver.propagation.getClass() == AC.class ? ((AC) head.solver.propagation).guaranteed : "");
		m.separator();
		m.put(WCK, head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	private InformationBloc preproInfo() {
		InformationBloc m = new InformationBloc(PREPROCESSING);
		m.put(N_EFFECTIVE, head.problem.features.nEffectiveFilterings);
		m.put(REVISIONS, "(" + stats.nRevisions() + ",useless=" + stats.nUselessRevisions() + ")", stats.nRevisions() > 0);
		m.put(N_ENTAILED, head.solver.entailed.size());
		m.put(N_VALUES, Variable.nValidValuesFor(head.problem.variables));

		Propagation propagation = head.solver.propagation;
		m.put(REMOVED_BY_AC, propagation instanceof AC ? ((AC) (propagation)).preproRemovals : 0);
		// m.put("nTotalRemovedValues", nPreproRemovedValues);
		m.put(N_SINGLETONS, Variable.nSingletonsIn(head.problem.variables));
		m.put(UNSAT, head.solver.stopping == Stopping.FULL_EXPLORATION);
		m.separator(stats.preprocessing.nRemovedTuples > 0 || stats.preprocessing.nAddedNogoods > 0 || stats.preprocessing.nAddedCtrs > 0);
		m.put(N_REMOVED_TUPLES, stats.preprocessing.nRemovedTuples);
		m.put(N_NOGOODS, stats.preprocessing.nAddedNogoods);
		m.put(N_ADDED_CTRS, stats.preprocessing.nAddedCtrs);
		m.separator(propagation.nSingletonTests > 0);
		m.put(N_SINGLETON_TESTS, propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, propagation.nEffectiveSingletonTests);
		m.put(N_BRANCHES, propagation instanceof SACGreedy ? ((SACGreedy) (propagation)).nBranchesBuilt : 0);
		m.put(SUM_BRANCHES, propagation instanceof SACGreedy ? ((SACGreedy) (propagation)).sumBranchSizes : 0);
		m.separator();
		m.put(SOLS, head.solver.solutions.found);
		m.put(SOL1_CPU, stats.times.firstSolCpu / 1000.0, head.solver.solutions.found > 0);
		m.put(WCK, stats.times.preproWck / 1000.0);
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	private InformationBloc runInfo() {
		InformationBloc m = new InformationBloc(RUN);
		m.put(RUN, head.solver.restarter.numRun + 1);
		m.put(DEPTHS, head.solver.minDepth + ".." + head.solver.maxDepth);
		String rb1 = head.solver.heuristic instanceof RunRobin ? ((RunRobin) head.solver.heuristic).current.getClass().getSimpleName() : "";
		String rb2 = head.control.valh.clazz.equals("RunRobin") ? ((HeuristicValuesDirect.RunRobin) head.problem.variables[0].heuristic).currentClass() : "";
		m.put("robin", rb1 + (rb1.length() > 0 && rb2.length() > 0 ? "-" : "") + rb2);

		if (head.control.varh.arrayPriorityRunRobin) {
			int index = head.solver.restarter.numRun % (head.problem.varArrays.length + 1);
			m.put("aprr", index == 0 ? "_" : head.problem.varArrays[index - 1].id);
		}
		m.put(N_EFFECTIVE, features.nEffectiveFilterings);
		m.put("asgs", stats.infoARunAssignemnts());
		// m.put("less", stats.nImpactlessAssignmentsBeforeRun);
		m.put(N_FAILED, stats.nFailedAssignments);
		m.put(N_WRONG, stats.nWrongDecisions);
		if (Kit.memory() > 10000000000L)
			m.put(MEM, Kit.memoryInMb());
		m.put(WCK, head.instanceStopwatch.wckTimeInSecondsForRun(wckBeforeSearch));
		m.put(N_NOGOODS, head.solver.nogoodReasoner != null ? head.solver.nogoodReasoner.nNogoods : 0);
		if (head.solver.solutions.found > 0) {
			m.put(SOLS, head.solver.solutions.found);
			if (head.problem.framework == TypeFramework.COP) {
				if (head.problem.optimizer.minBound == 0 || head.problem.optimizer.minBound == Long.MIN_VALUE)
					m.put(BOUND, head.solver.solutions.bestBound + head.problem.optimizer.gapBound);
				else
					m.put(BOUNDS, head.problem.optimizer.stringBounds());
			}
		}
		m.put("cntCBval", HeuristicValues.cntCBval);
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
		IpsReasoner ipsReasoner = head.solver.ipsReasoner;
		if (ipsReasoner instanceof IpsReasonerEquivalence && !ipsReasoner.stopped) {
			m.put(MAP_SIZE, ((IpsReasonerEquivalence) ipsReasoner).mapOfHashKeys.size());
			m.put(N_INFERENCES, ((IpsReasonerEquivalence) ipsReasoner).nInferences);
			m.put(N_TOO_LARGE_KEYS, ((IpsReasonerEquivalence) ipsReasoner).nTooLargeKeys);
		}
		if (ipsReasoner != null) {
			IpsExtractor extractor = ipsReasoner.extractor;
			m.put(N_SELIMINABLES, decimalFormat.format(extractor.proportionOfSEliminableVariables()));
			m.put(N_RELIMINABLES, decimalFormat.format(extractor.proportionOfREliminableVariables()));
			m.put(N_IELIMINABLES, decimalFormat.format(extractor.proportionOfIEliminableVariables()));
			m.put(N_DELIMINABLES, decimalFormat.format(extractor.proportionOfDEliminableVariables()));
			m.put(N_PELIMINABLES, decimalFormat.format(extractor.proportionOfPEliminableVariables()));
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
		m.put("noefs", stats.nImpactlessAssignments);
		m.put(N_NOGOODS, head.solver.nogoodReasoner != null ? head.solver.nogoodReasoner.nNogoods : 0);
		m.separator();
		m.put(STOP, head.solver.stopping == null ? "no" : head.solver.stopping.toString());
		m.put(N_WRONG, stats.nWrongDecisions);
		if (head.solver.solutions.found > 0) {
			if (head.problem.framework != TypeFramework.CSP) {
				m.put(BOUND, head.solver.solutions.bestBound);
				m.put(BOUND_WCK, stats.times.lastSolWck / 1000.0);
				// m.put(BOUND_CPU, stats.times.lastSolCpu / 1000.0);
			}
			m.put(SOLS, head.solver.solutions.found);
			m.put(SOL1_CPU, stats.times.firstSolCpu / 1000.0);
		}
		m.separator();
		m.put(WCK, head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

}
