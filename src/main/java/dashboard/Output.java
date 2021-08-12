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

import interfaces.Observers.ObserverConstruction;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import main.Head;
import problem.Features.Attributes;
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

	private final Head head;

	private Document document;

	private Element root, resolElt, solverElt;

	private String outputFileName;

	public Output(Head head, String configFileName) {
		this.head = head;
		if (!head.control.xml.dirForCampaign.equals(EMPTY_STRING)) {
			document = Kit.createNewDocument();
			root = document.createElement(TypeOutput.RESOLUTIONS.toString());
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

	// public String record(TypeOutput output, MapAtt map, Element parent) {
	// record(output, map.entries(), parent);
	// return map.toString();
	// }

	public void beforeData() { // not a method from an observer
		resolElt = record(TypeOutput.RESOLUTION, null, root);
		save(head.instanceStopwatch.wckTime());
	}

	public void afterData() { // not a method from an observer
		Attributes ia = head.problem.features.instanceAttributes(head.instanceNumber);

		String name = ia.entries().stream().filter(e -> e.getKey().equals(NAME)).map(e -> e.getValue().toString()).findFirst().get();
		outputFileName = outputFileNameFrom(name, head.control.settingsFilename);

		Kit.log.config(COMMENT_PREFIX + Kit.preprint("Instance ", Kit.BLUE) + name + "\n");
		record(TypeOutput.INSTANCE, ia.entries(), resolElt);
	}

	@Override
	public void afterProblemConstruction() {
		Kit.control(head.problem.variables.length > 0, () -> "No variable in your model");
		Attributes da = head.problem.features.domainsAttributes();
		Attributes va = head.problem.features.variablesAttributes();
		Attributes ca = head.problem.features.constraintsAttributes();
		Attributes oa = head.problem.optimizer != null ? head.problem.features.objectiveAttributes() : null;
		record(TypeOutput.DOMAINS, da.entries(), resolElt);
		record(TypeOutput.VARIABLES, va.entries(), resolElt);
		record(TypeOutput.CONSTRAINTS, ca.entries(), resolElt);
		if (oa != null)
			record(TypeOutput.OBJECTIVE, oa.entries(), resolElt);
		Kit.log.config("\n" + da.toString());
		Kit.log.config(va.toString());
		Kit.log.config(ca.toString());
		if (oa != null)
			Kit.log.config(oa.toString());
	}

	@Override
	public void afterSolverConstruction() {
		Attributes sa = head.solver.stats.solverAttributes();
		solverElt = record(TypeOutput.SOLVER, sa.entries(), resolElt);
		Kit.log.config("\n" + sa.toString());
	}

	@Override
	public final void afterPreprocessing() {
		Attributes pa = head.solver.stats.preproAttributes();
		record(TypeOutput.PREPROCESSING, pa.entries(), solverElt);
		Kit.log.config("\n" + pa.toString() + "\n");
	}

	@Override
	public final void afterRun() {
		Attributes ra = head.solver.stats.runAttributes();
		record(TypeOutput.RUN, ra.entries(), solverElt);
		Kit.log.config(ra.toString());
	}

	@Override
	public final void afterSolving() {
		Attributes ga = head.solver.stats.globalAttributes();
		record(TypeOutput.GLOBAL, ga.entries(), solverElt);
		Kit.log.config("\n" + ga.toString());
	}

	public String save(long totalWck) {
		if (document == null)
			return null;
		root.setAttribute(TOTAL_WCK_TIME, totalWck + "");
		String dirName = head.control.xml.dirForCampaign + File.separator + RESULTS_DIRECTORY;
		File file = new File(dirName);
		if (!file.exists())
			file.mkdirs();
		return Utilities.save(document, dirName + File.separator + outputFileName);
	}
}
