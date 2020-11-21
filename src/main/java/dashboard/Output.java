/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package dashboard;

import static org.xcsp.common.Constants.EMPTY_STRING;

import java.io.File;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Collection;
import java.util.Map.Entry;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import interfaces.Observers.ObserverConstruction;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import main.Head;
import problem.ProblemStuff.MapAtt;
import propagation.GAC;
import utility.DocumentHandler;
import utility.Enums.TypeOutput;
import utility.Kit;

/**
 * The role of this class is to output data concerning the resolution of problem instances. These data are collected by means of a XML document that may be
 * saved and/or directly displayed at screen.
 */
public class Output implements ObserverConstruction, ObserverSearch, ObserverRuns {

	/**********************************************************************************************
	 * Constants
	 *********************************************************************************************/

	public static final String RESULTS_DIRECTORY_NAME = "results";
	public static final String CONFIGURATION_DIRECTORY_NAME = "configurations";
	public static final String CONTEXT_DIRECTORY_NAME = "context";

	// Resolutions

	public static final String MULTITHREAD_RESULTS = "multithreadResults";
	public static final String CONFIGURATION_FILE_NAME = "configurationFileName";
	public static final String TOTAL_WCK_TIME = "totalWckTime";
	public static final String TOTAL_CPU_TIME = "totalCpuTime";
	public static final String LEVEL = "level";

	// Instance

	public static final String OBJECTIVE = "objective";
	public static final String NUMBER = "number";
	public static final String FRAMEWORK = "framework";
	public static final String NAME = "name";
	public static final String PARAMETERS = "parameters";
	public static final String N_VARIABLES = "nVariables";
	public static final String N_DISCARDED_VARIABLES = "nDiscardedVariables";
	public static final String N_DOMAIN_TYPES = "nDomainTypes";
	public static final String N_CONSTRAINTS = "nConstraints";
	public static final String N_DISCARDED_CONSTRAINTS = "nDiscardedConstraints";
	public static final String N_RELATION_TYPES = "nRelationTypes";
	public static final String N_PRESENT_UNARY_CONSTRAINTS = "nPresentUnaryConstraints";
	public static final String N_REMOVED_UNARY_CONSTRAINTS = "nRemovedUnaryConstraints";
	public static final String N_IGNORED_UNARY_CONSTRAINTS = "nIgnoredUnaryConstraints";
	public static final String N_GLOBAL_CONSTRAINTS = "nGlobalConstraints";
	public static final String N_SPECIFIC_CONSTRAINTS = "nSpecificConstraints";
	public static final String N_MERGED_CONSTRAINTS = "nMergedConstraints";
	public static final String N_UNIVERSAL_CONSTRAINTS = "nUniversalConstraints";
	public static final String N_ADDED_CONSTRAINTS = "nAddedConstraints";
	public static final String N_ISOLATED_VARIABLES = "nIsolatedVariables";
	public static final String N_FIXED_VARIABLES = "nFixedVariables";
	public static final String N_VALUES_REMOVED_AT_CONSTRUCTION = "nValuesRemovedAtConstruction";
	public static final String N_PURGED_VALUES = "nPurgedValues";
	public static final String N_CONFLICTS_STRUCTURES = "nConflictsStructures";
	public static final String N_SHARED_CONFLICTS_STRUCTURES = "nSharedConflictsStructures";
	public static final String N_UNBUILT_CONFLICTS_STRUCTURES = "nUnbuiltConflictsStructures";
	public static final String N_EXTENSION_STRUCTURES = "nExtensionStructures";
	public static final String N_SHARED_EXTENSION_STRUCTURES = "nSharedExtensionStructures";
	public static final String N_SHARED_BINARY_REPRESENTATIONS = "nSharedBinaryRepresentations";
	public static final String N_CONVERTED_CONSTRAINTS = "nConvertedConstraints";
	public static final String N_CONVERT_CONSTRAINTS_CHECKS = "nConvertConstraintsChecks";
	public static final String N_EVALUATION_MANAGERS = "nEvaluationManagers";
	public static final String N_SHARED_EVALUATION_MANAGERS = "nSharedEvaluationManagers";
	public static final String MIN_DEGREE = "minDegree";
	public static final String DEGREES = "degrees";
	public static final String MAX_DEGREE = "maxDegree";
	public static final String DOMAIN_SIZES = "domainSizes";
	public static final String N_TOTAL_VALUES = "nTotalValues";
	public static final String ARITIES = "arities";
	public static final String MAX_CONSTRAINT_TUPLES = "maxConstraintTuples";
	public static final String TYPES = "types";
	public static final String TABLES = "tables";
	public static final String DEFAULT_COSTS = "defaultCosts";
	public static final String N_TOTAL_TUPLES = "nTotalTuples";
	public static final String TOTAL_INITIAL_SPACE = "totalInitialSpace";
	public static final String TOTAL_REDUCED_SPACE = "totalReducedSpace";
	public static final String WCK_MINING = "wckMining";
	public static final String COMPRESSION = "compression";

	// solver

	public static final String WCK = "wck";
	public static final String CPU = "cpu";
	public static final String MEM = "mem";
	public static final String FREE_MEMORY = "freeMemory";
	public static final String MAX_MEMORY = "maxMemory";
	public static final String ALLOCATED_MEMORY = "allocatedMemory";
	public static final String GUARANTEED_GAC = "guaranteedGAC";

	// preprocessing

	public static final String N_CONSTRAINT_CHECKS = "nConstraintChecks";
	public static final String N_INITIAL_CHECKS = "nInitialChecks";
	public static final String N_RESTORATIONS = "nRestorations";
	public static final String DEPTH = "depth";
	public static final String MIN = "min";
	public static final String MAX = "max";
	public static final String AVG = "avg";
	public static final String N_EFFECTIVE_FILTERINGS = "nEffectivePFilterings";
	public static final String N_REVISIONS = "nRevisions";
	public static final String N_USELESS_REVISIONS = "nUselessRevisions";
	public static final String N_SINGLETON_TESTS = "nSingletonTests";
	public static final String N_EFFECTIVE_SINGLETON_TESTS = "nEffectiveSingletonTests";
	public static final String N_NC_REMOVALS = "nNCRemovals";
	public static final String N_AC_REMOVALS = "nACRemovals";
	public static final String N_SUB_REMOVALS = "nSUBRemovals";
	public static final String AVG_SUB_REMOVALS = "avgSUBRemovals";
	public static final String N_FOUND_SINGLETONS = "nFoundSingletons";
	public static final String N_BUILT_BRANCHES = "nBuiltBranches";
	public static final String SUM_BRANCH_SIZES = "sumBranchSizes";
	public static final String N_REMOVED_VALUES = "nRemovedValues";
	public static final String N_REMOVED_TUPLES = "nRemovedTuples";
	public static final String N_VALID_SUPPORTS = "nValidSupports";
	public static final String DETECTED_INCONSISTENCY = "detectedInconsistency";
	public static final String GLOBAL_CPU_TIME = "globalCpuTime";

	// search

	public static final String RUN = "run";
	public static final String N_ASSIGNMENTS = "nAssignments";
	public static final String N_FAILED_ASSIGNMENTS = "nFailedAssignments";
	public static final String AVG_FAILED_DEPTH = "avgFailedDepth";
	public static final String N_WRONG = "wrong";
	public static final String N_BACKTRACKS = "nBacktracks";
	public static final String N_NODES = "nNodes";
	public static final String N_ADDED_NOGOODS = "nAddedNogoods";
	public static final String N_INFERRED_BACKTRACKS = "nInferredBacktracks";
	public static final String N_INFERRED_REMOVALS = "nInferredRemovals";
	public static final String MAP_SIZE = "mapSize";
	public static final String N_INFERENCES = "nInferences";
	public static final String N_TOO_LARGE_KEYS = "nTooLargeKeys";
	public static final String N_SELIMINABLES = "nSEliminables";
	public static final String N_RELIMINABLES = "nREliminables";
	public static final String N_DELIMINABLES = "nDEliminables";
	public static final String N_IELIMINABLES = "nIEliminables";
	public static final String N_PELIMINABLES = "nPEliminables";
	public static final String N_FILTER_CALLS = "nFilterCalls";
	public static final String AVG_TABLE_PROPORTION = "avgTableProportion";
	public static final String AVG_TABLE_SIZE = "avgTableSize";

	// global

	public static final String WALL_CLOCK_TIME_TO_BUILD_PROBLEM = "wckTimeToBuildProblem";
	public static final String WALL_CLOCK_TIME_TO_BUILD_SOLVER = "wckTimeToBuildSolver";
	public static final String BUILDING_CPU_TIME = "buildingCpuTime";
	public static final String BUILDING_WALL_CLOCK_TIME = "buildingWckTime";
	public static final String N_GENERATORS = "nGenerators";
	public static final String SYMMETRY_CPU_TIME = "symmetryCpuTime";
	public static final String SYMMETRY_WALL_CLOCK_TIME = "symmetryWckTime";
	public static final String N_CLIQUES = "nCliques";
	public static final String SOLVING_CPU_TIME = "solvingCpuTime";
	public static final String SOLVING_WALL_CLOCK_TIME = "solvingWckTime";
	public static final String FIRST_SOLUTION_CPU_TIME = "firstSolutionCpuTime";
	public static final String FIRST_SOLUTION_WALL_CLOCK_TIME = "firstSolutionWckTime";
	public static final String EXPIRED_TIME = "expiredTime";
	public static final String TOTAL_EXPLORATION = "totalExploration";
	public static final String N_FOUND_SOLUTIONS = "foundSolutions";
	public static final String BEST_BOUND = "bestBound";
	public static final String BEST_BOUND_CPU_TIME = "bestBoundCpuTime";
	public static final String BEST_BOUND_WALL_CLOCK_TIME = "bestBoundWckTime";
	public static final String STOP = "Stop";

	// statistics

	public static final String N_INSTANCES = "nInstances";
	public static final String PREPRO_CPU_TIME = "preproCpuTime";
	public static final String PREPRO_WCK_TIME = "preproWckTime";
	public static final String SEARCH_CPU_TIME = "searchCpuTime";
	public static final String SEARCH_WCK_TIME = "searchWckTime";
	public static final String MEDIAN_CPU_TIME = "medianCpuTime";
	public static final String N_PREPRO_INCONSISTENCIES = "nPreproInconsistencies";

	// cores

	public static final String GLOBAL_TIME = "globalTime";
	public static final String MODE = "mode";
	public static final String N_RUNS = "nRuns";
	public static final String N_CORES = "nCores";
	public static final String N_VAVG = "nVAvg";
	public static final String N_CAVG = "nCAvg";
	public static final String LAST_CORES = "lastCores";

	public static final String DATA_SEPARATOR = "  ";

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static String getOutputFileNamePrefixFrom(String fullInstanceName, String fullConfigurationName) {
		return Kit.getRawInstanceName(fullInstanceName) + (fullConfigurationName != null ? "_" + Kit.getXMLBaseNameOf(fullConfigurationName) + "_" : "");
	}

	/**********************************************************************************************
	 * Fields and methods
	 *********************************************************************************************/

	private final Head resolution;

	private Document document;

	private Element root, resolElt, solverElt;

	private String outputFileName;

	public static final String COMMENT_PREFIX = "  ";

	public Output(Head resolution, String configFileName) {
		this.resolution = resolution;
		if (resolution.control.settingXml.dirForCampaign.equals(EMPTY_STRING) == false) {
			document = DocumentHandler.createNewDocument();
			root = document.createElement(TypeOutput.RESOLUTIONS.toString());
			root.setAttribute(Output.CONFIGURATION_FILE_NAME, configFileName);
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

	// public String record(TypeOutput output, MapAtt map, Element parent) {
	// record(output, map.entries(), parent);
	// return map.toString();
	// }

	public void beforeData() { // not a method from an observer
		resolElt = record(TypeOutput.RESOLUTION, null, root);
		save(resolution.instanceStopwatch.wckTime());
	}

	public void afterData() { // not a method from an observer
		MapAtt ia = resolution.problem.stuff.instanceAttributes(resolution.instanceNumber);
		if (outputFileName == null) {
			String name = ia.entries().stream().filter(e -> e.getKey().equals(Output.NAME)).map(e -> e.getValue().toString()).findFirst().get();
			outputFileName = outputFileNameFrom(name, resolution.control.settingsFilename);
		}
		Kit.log.config(ia.toString() + "\n");
		record(TypeOutput.INSTANCE, ia.entries(), resolElt);
	}

	@Override
	public void afterProblemConstruction() {
		Kit.control(resolution.problem.variables.length > 0, () -> "No variable in your model");
		MapAtt da = resolution.problem.stuff.domainsAttributes();
		MapAtt va = resolution.problem.stuff.variablesAttributes();
		MapAtt ca = resolution.problem.stuff.ctrsAttributes();
		MapAtt oa = resolution.problem.optimizer != null ? resolution.problem.stuff.objsAttributes() : null;
		record(TypeOutput.DOMAINS, da.entries(), resolElt);
		record(TypeOutput.VARIABLES, va.entries(), resolElt);
		record(TypeOutput.CONSTRAINTS, ca.entries(), resolElt);
		if (oa != null)
			record(TypeOutput.OBJECTIVE, oa.entries(), resolElt);
		Kit.log.config("\n\n" + da.toString());
		Kit.log.config(va.toString());
		Kit.log.config(ca.toString());
		if (oa != null)
			Kit.log.config(oa.toString());
	}

	@Override
	public void afterSolverConstruction() {
		MapAtt sa = new MapAtt("Solver");
		if (resolution.solver.propagation.getClass() == GAC.class)
			sa.put(Output.GUARANTEED_GAC, Constraint.isGuaranteedGAC(resolution.problem.constraints));
		sa.separator();
		sa.put(Output.WCK, resolution.instanceStopwatch.wckTimeInSeconds());
		sa.put(Output.CPU, resolution.stopwatch.cpuTimeInSeconds());
		sa.put(Output.MEM, Kit.memoryInMb());
		solverElt = record(TypeOutput.SOLVER, sa.entries(), resolElt);
		Kit.log.config("\n" + sa.toString());
	}

	@Override
	public final void afterPreprocessing() {
		MapAtt pa = resolution.solver.stats.preproAttributes();
		record(TypeOutput.PREPROCESSING, pa.entries(), solverElt);
		Kit.log.config("\n" + pa.toString() + "\n");
	}

	@Override
	public final void afterRun() {
		MapAtt ra = resolution.solver.stats.runAttributes();
		record(TypeOutput.RUN, ra.entries(), solverElt);
		Kit.log.config(ra.toString());
	}

	@Override
	public final void afterSolving() {
		MapAtt ga = resolution.solver.stats.globalAttributes();
		record(TypeOutput.GLOBAL, ga.entries(), solverElt);
		Kit.log.config(ga.toString());
	}

	public String save(long totalWck) {
		if (document == null)
			return null;
		root.setAttribute(Output.TOTAL_WCK_TIME, totalWck + "");
		String dirName = resolution.control.settingXml.dirForCampaign + File.separator + Output.RESULTS_DIRECTORY_NAME;
		File file = new File(dirName);
		if (!file.exists())
			file.mkdirs();
		return Utilities.save(document, dirName + File.separator + outputFileName);
	}
}
