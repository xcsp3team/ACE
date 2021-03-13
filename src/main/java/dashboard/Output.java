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
import problem.Features.MapAtt;
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
	public static final String RUN = "Run";
	public static final String NUMBER = "number";
	public static final String NAME = "name";
	public static final String NTYPES = "nTypes";
	public static final String NVALUES = "nValues";
	public static final String COUNT = "count";
	public static final String DEGREES = "degrees";
	public static final String ARITIES = "arities";
	public static final String SIZES = "sizes";
	public static final String TYPES = "types";
	public static final String TABLES = "tables";
	public static final String BOUNDS = "bounds";

	public static final String WCK = "wck";
	public static final String CPU = "cpu";
	public static final String MEM = "mem";

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
		MapAtt ia = head.problem.features.instanceAttributes(head.instanceNumber);

		String name = ia.entries().stream().filter(e -> e.getKey().equals(NAME)).map(e -> e.getValue().toString()).findFirst().get();
		outputFileName = outputFileNameFrom(name, head.control.settingsFilename);

		Kit.log.config(COMMENT_PREFIX + Kit.preprint("Instance ", Kit.BLUE) + name + "\n");
		record(TypeOutput.INSTANCE, ia.entries(), resolElt);
	}

	@Override
	public void afterProblemConstruction() {
		Kit.control(head.problem.variables.length > 0, () -> "No variable in your model");
		MapAtt da = head.problem.features.domainsAttributes();
		MapAtt va = head.problem.features.variablesAttributes();
		MapAtt ca = head.problem.features.ctrsAttributes();
		MapAtt oa = head.problem.optimizer != null ? head.problem.features.objsAttributes() : null;
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
		MapAtt sa = head.solver.stats.solverConstructionAttributes();
		solverElt = record(TypeOutput.SOLVER, sa.entries(), resolElt);
		Kit.log.config("\n" + sa.toString());
	}

	@Override
	public final void afterPreprocessing() {
		MapAtt pa = head.solver.stats.preproAttributes();
		record(TypeOutput.PREPROCESSING, pa.entries(), solverElt);
		Kit.log.config("\n" + pa.toString() + "\n");
	}

	@Override
	public final void afterRun() {
		MapAtt ra = head.solver.stats.runAttributes();
		record(TypeOutput.RUN, ra.entries(), solverElt);
		Kit.log.config(ra.toString());
	}

	@Override
	public final void afterSolving() {
		MapAtt ga = head.solver.stats.globalAttributes();
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
