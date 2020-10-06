/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package tools.output;

import static utility.Enums.TypeOutput.ALL;
import static utility.Enums.TypeOutput.CONSTRAINTS;
import static utility.Enums.TypeOutput.CRASHED;
import static utility.Enums.TypeOutput.ERROR;
import static utility.Enums.TypeOutput.GLOBAL;
import static utility.Enums.TypeOutput.INSTANCE;
import static utility.Enums.TypeOutput.KERNEL;
import static utility.Enums.TypeOutput.PREPROCESSING;
import static utility.Enums.TypeOutput.RESOLUTION;
import static utility.Enums.TypeOutput.RESOLUTIONS;
import static utility.Enums.TypeOutput.SEARCH;
import static utility.Enums.TypeOutput.SOLVER;
import static utility.Enums.TypeOutput.VARIABLES;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xcsp.common.Utilities;

import dashboard.Output;
import utility.Enums.EStopping;
import utility.Enums.TypeOutput;
import utility.Kit;
import utility.Reflector;
import utility.XMLManager;

@SuppressWarnings("unused")
public class CreateCampagnDataFile {

	// ************************************************************************
	// ***** Metrics
	// ************************************************************************

	private Metric cpu = new MetricDouble(GLOBAL, Output.CPU, 1000);
	private Metric pcpu = new MetricDouble(PREPROCESSING, Output.CPU, 1000);
	private Metric scpu = new MetricDouble(SEARCH, Output.CPU, 1000);
	private Metric mem = new MetricLongMem(GLOBAL, Output.MEM);
	private Metric pmem = new MetricLongMem(PREPROCESSING, Output.MEM);
	private Metric smem = new MetricLongMem(SEARCH, Output.MEM);

	private Metric nbVariables = new MetricLong(VARIABLES, Output.N_VARIABLES);
	private Metric nbDomainTypes = new MetricLong(VARIABLES, Output.N_DOMAIN_TYPES);
	private Metric nbTotalValues = new MetricLong(VARIABLES, Output.N_TOTAL_VALUES);

	private Metric nbConstraints = new MetricLong(CONSTRAINTS, Output.N_CONSTRAINTS);
	private Metric nbGenerators = new MetricLong(CONSTRAINTS, Output.N_GENERATORS);
	private Metric symmetryCpuTime = new MetricDouble(CONSTRAINTS, Output.SYMMETRY_CPU_TIME);

	private Metric nbAcRemovals = new MetricLong(PREPROCESSING, Output.N_AC_REMOVALS);
	private Metric nbRemovedValues = new MetricLong(PREPROCESSING, Output.N_REMOVED_VALUES);
	private Metric nbSubRemovals = new MetricLong(PREPROCESSING, Output.N_SUB_REMOVALS);
	private Metric nbRemovedTuples = new MetricLong(PREPROCESSING, Output.N_REMOVED_TUPLES);
	private Metric nbAddedConstraints = new MetricLong(PREPROCESSING, Output.N_ADDED_CONSTRAINTS);
	private Metric nbSingletonTests = new MetricLong(PREPROCESSING, Output.N_SINGLETON_TESTS);
	private Metric nbEffectiveSingletonTests = new MetricLong(PREPROCESSING, Output.N_EFFECTIVE_SINGLETON_TESTS);
	private Metric nbFoundSingletons = new MetricLong(PREPROCESSING, Output.N_FOUND_SINGLETONS);
	private Metric nbBuiltBranches = new MetricLong(PREPROCESSING, Output.N_BUILT_BRANCHES);
	private Metric sumBranchSizes = new MetricLong(PREPROCESSING, Output.SUM_BRANCH_SIZES);
	private Metric detectedInconsistency = new MetricEquals(PREPROCESSING, Output.DETECTED_INCONSISTENCY, "yes");

	private Metric nbWrong = new MetricLong(GLOBAL, Output.N_WRONG);
	// private Metric nbAssignments = new MetricLong(SEARCH, Output.NB_ASSIGNMENTS);
	private Metric mapSize = new MetricLong(SEARCH, Output.MAP_SIZE);
	private Metric nbInferences = new MetricLong(SEARCH, Output.N_INFERENCES);
	private Metric nbSEliminables = new MetricDouble(SEARCH, Output.N_SELIMINABLES);
	private Metric nbREliminables = new MetricDouble(SEARCH, Output.N_RELIMINABLES);
	private Metric nbDEliminables = new MetricDouble(SEARCH, Output.N_DELIMINABLES);
	private Metric nbIEliminables = new MetricDouble(SEARCH, Output.N_IELIMINABLES);
	private Metric nbPEliminables = new MetricDouble(SEARCH, Output.N_PELIMINABLES);

	private Metric nbSolutions = new MetricLong(GLOBAL, Output.N_FOUND_SOLUTIONS);
	private Metric nbConstraintChecks = new MetricLong(GLOBAL, Output.N_CONSTRAINT_CHECKS);
	private Metric bestBound = new MetricLong(GLOBAL, Output.BEST_BOUND);
	private Metric bestBoundCpuTime = new MetricDouble(GLOBAL, "bestBoundCpu", 1000);
	private Metric expiredTime = new MetricEquals(GLOBAL, Output.EXPIRED_TIME, "yes");
	private Metric nbEffectivePropagations = new MetricLong(GLOBAL, Output.N_EFFECTIVE_FILTERINGS);
	private Metric avgSubRemovals = new MetricDouble(GLOBAL, Output.AVG_SUB_REMOVALS);
	private Metric nbFilterCalls = new MetricLong(GLOBAL, Output.N_FILTER_CALLS);
	private Metric avgTableProportion = new MetricDouble(GLOBAL, Output.AVG_TABLE_PROPORTION, 1000);
	private Metric avgTableSize = new MetricDouble(GLOBAL, Output.AVG_TABLE_SIZE);
	private Metric totalInitialSpace = new MetricLong(GLOBAL, Output.TOTAL_INITIAL_SPACE);
	private Metric totalReducedSpace = new MetricLong(GLOBAL, Output.TOTAL_REDUCED_SPACE);
	private Metric wckMining = new MetricLong(GLOBAL, Output.WCK_MINING);
	private Metric exceededTime = new MetricEquals(GLOBAL, Output.STOP, EStopping.EXCEEDED_TIME.toString());
	private Metric global_nbSingletonTests = new MetricLong(GLOBAL, Output.N_SINGLETON_TESTS);
	private Metric global_nbEffectiveSingletonTests = new MetricLong(GLOBAL, Output.N_EFFECTIVE_SINGLETON_TESTS);

	private Metric all_cpu = new MetricDouble(ALL, Output.CPU, 1000);
	private Metric all_wckPREPROCESSING = new MetricDouble(ALL, Output.PREPRO_WCK_TIME, 1000);
	private Metric all_wckSearch = new MetricDouble(ALL, Output.SEARCH_WCK_TIME, 1000);
	private Metric all_mem = new MetricLong(ALL, Output.MEM);
	private Metric all_nbAssignments = new MetricDouble(ALL, Output.N_ASSIGNMENTS);
	private Metric all_nbSolutions = new MetricDouble(ALL, Output.N_FOUND_SOLUTIONS);
	private Metric all_nbFilterCalls = new MetricDouble(ALL, Output.N_FILTER_CALLS);
	private Metric all_avgTableProportion = new MetricDouble(ALL, Output.AVG_TABLE_PROPORTION, 1000);
	private Metric all_avgTableSize = new MetricDouble(ALL, Output.AVG_TABLE_SIZE);
	private Metric all_nbRemovedValues = new MetricDouble(ALL, Output.N_REMOVED_VALUES);
	private Metric all_nbRemovedTuples = new MetricDouble(ALL, Output.N_REMOVED_TUPLES);
	private Metric all_nbValidSupports = new MetricDouble(ALL, Output.N_VALID_SUPPORTS);
	private Metric all_nbInstances = new MetricLong(ALL, Output.N_INSTANCES);

	private Metric all_nbVals = new MetricDouble(ALL, "nbVals");
	private Metric all_nbUnks = new MetricDouble(ALL, "nbUnks");
	private Metric all_nbUnksAfterAC = new MetricDouble(ALL, "nbUnksAfterAC");
	private Metric all_nbTests = new MetricDouble(ALL, "nbTests");

	private Metric nbCrashes = new MetricLong(CRASHED, Output.N_INSTANCES);

	// ************************************************************************
	// ***** Intern classes of Metrics
	// ************************************************************************

	private abstract class Metric {
		protected TypeOutput elementType;
		protected String attribute;

		protected Metric(TypeOutput elementType, String attribute) {
			this.elementType = elementType;
			this.attribute = attribute;
		}

		protected abstract Number getValue();
	}

	private class MetricLong extends Metric {
		private MetricLong(TypeOutput elementType, String attribute) {
			super(elementType, attribute);
		}

		@Override
		protected Number getValue() {
			Element element = storedElements[elementType.ordinal()];
			return element == null ? CreateLatexTable.ABSENT : Long.parseLong("0" + element.getAttribute(attribute));
		}
	}

	private class MetricLongMem extends Metric {
		private MetricLongMem(TypeOutput elementType, String attribute) {
			super(elementType, attribute);
		}

		@Override
		protected Number getValue() {
			Element element = storedElements[elementType.ordinal()];
			if (element == null)
				return CreateLatexTable.ABSENT;
			StringTokenizer st = new StringTokenizer(element.getAttribute(attribute), "M");
			return Long.parseLong(st.nextToken()) * 1000000 + Long.parseLong(st.nextToken()) * 1000;
		}
	}

	private class MetricDouble extends Metric {
		private int multiplier;

		private MetricDouble(TypeOutput elementType, String attribute, int multiplier) {
			super(elementType, attribute);
			this.multiplier = multiplier;
		}

		private MetricDouble(TypeOutput elementType, String attribute) {
			this(elementType, attribute, 1);
		}

		@Override
		protected Number getValue() {
			Element element = storedElements[elementType.ordinal()];
			return element == null ? CreateLatexTable.ABSENT : Double.parseDouble("0" + element.getAttribute(attribute)) * multiplier;
		}
	}

	private class MetricEquals extends Metric {
		private String value;

		private MetricEquals(TypeOutput elementType, String attribute, String value) {
			super(elementType, attribute);
			this.value = value;
		}

		@Override
		protected Number getValue() {
			Element element = storedElements[elementType.ordinal()];
			return element == null ? CreateLatexTable.ABSENT : element.getAttribute(attribute).equals(value) ? 1 : 0;
		}
	}

	// ************************************************************************
	// ***** Body
	// ************************************************************************

	private Element[] storedElements = new Element[TypeOutput.values().length];

	private List<Metric> selectedMetrics;

	private Map<String, Map<String, String>> globalMap;

	private Set<String> keys;

	private boolean seriesExtraction, kernelExtraction;

	private String error;

	private Map<String, Long> nbSolutionsControl = new HashMap<>();

	private final boolean mustReachGoal;

	private int cnt = 0;

	private void insert(String instance, String method, String s) {
		// System.out.println("insert " + instance + " " + method);
		keys.add(method);
		Map<String, String> instanceMap = globalMap.computeIfAbsent(instance, k -> new TreeMap<>());
		String value = instanceMap.get(method);
		if (value == null || value.equals(error))
			instanceMap.put(method, s);
	}

	private void selectMetrics(Metric... metrics) {
		selectedMetrics = new ArrayList<>();
		for (int i = 0; i < metrics.length; i++)
			selectedMetrics.add(metrics[i]);
	}

	private Element firstComponentOf(Element element, TypeOutput outputElement) {
		return (Element) element.getElementsByTagName(outputElement.toString()).item(0);
	}

	private Element firstComponentInstanceNameOf(Element element) {
		Element elt = firstComponentOf(element, INSTANCE);
		if (elt != null)
			return elt;
		return (Element) element.getElementsByTagName("Instance").item(0);
	}

	private Element lastComponentOf(Element element, TypeOutput outputElement) {
		NodeList nodeList = element.getElementsByTagName(outputElement.toString());
		return nodeList.getLength() == 0 ? null : (Element) nodeList.item(nodeList.getLength() - 1);
	}

	private void dealWithInstance(Element resolution, String instanceName, String configurationFileName) {
		// System.out.println(instanceName + " " + configurationFileName);

		boolean csp = firstComponentOf(resolution, INSTANCE).getAttribute(Output.FRAMEWORK).startsWith("CSP");

		storedElements[VARIABLES.ordinal()] = firstComponentOf(resolution, VARIABLES);
		storedElements[CONSTRAINTS.ordinal()] = firstComponentOf(resolution, CONSTRAINTS);
		Element solver = lastComponentOf(resolution, SOLVER);
		if (solver != null) {
			storedElements[PREPROCESSING.ordinal()] = lastComponentOf(solver, PREPROCESSING);
			storedElements[SEARCH.ordinal()] = lastComponentOf(solver, SEARCH);
			storedElements[GLOBAL.ordinal()] = firstComponentOf(solver, GLOBAL);
		}
		StringBuilder selectedMetricsValues = new StringBuilder();
		boolean timeout = exceededTime.getValue().longValue() == 1;
		// System.out.println("timeout " + timeout);
		if (solver == null || firstComponentOf(resolution, ERROR) != null) {
			for (int i = 0; i < selectedMetrics.size(); i++)
				selectedMetricsValues.append(CreateLatexTable.ERROR).append(" ");
		} else if (mustReachGoal && timeout)
			for (int i = 0; i < selectedMetrics.size(); i++)
				selectedMetricsValues.append(CreateLatexTable.TIME_OUT).append(" ");
		else {
			for (Metric metric : selectedMetrics) {
				selectedMetricsValues.append(metric.getValue()).append(" ");
				if (metric == nbSolutions && csp) {
					if (!nbSolutionsControl.containsKey(instanceName)) {
						if (!timeout)
							nbSolutionsControl.put(instanceName, nbSolutions.getValue().longValue());
					} else {
						long nb = nbSolutionsControl.get(instanceName);
						if (!timeout && nb != nbSolutions.getValue().longValue() || timeout && nbSolutions.getValue().longValue() > nb)
							System.out.println(
									"************** Bug with " + instanceName + " " + exceededTime.getValue().longValue() + " " + configurationFileName);
					}
				}
			}
		}
		insert(instanceName, configurationFileName, selectedMetricsValues.toString());
	}

	private void dealWithSeries(Element resolutions, String instanceName, String configurationFileName) {
		storedElements[CRASHED.ordinal()] = firstComponentOf(resolutions, CRASHED);
		storedElements[ALL.ordinal()] = firstComponentOf(resolutions, ALL);

		StringBuilder selectedMetricsValues = new StringBuilder();
		if (firstComponentOf(resolutions, ALL) == null)
			for (int i = 0; i < selectedMetrics.size(); i++)
				selectedMetricsValues.append(CreateLatexTable.TIME_OUT).append(" ");
		else if (nbCrashes.getValue().longValue() > 0) {
			selectedMetricsValues.append(-nbCrashes.getValue().longValue()).append(" ");
			for (int i = 1; i < selectedMetrics.size(); i++)
				selectedMetricsValues.append(CreateLatexTable.CRASHED).append(" ");
		} else
			for (Metric metric : selectedMetrics)
				selectedMetricsValues.append(metric.getValue()).append(" ");
		// System.out.println(instanceName + " " + configurationFileName + " " + selectedMetricsValues);
		insert(instanceName, configurationFileName, selectedMetricsValues.toString());
	}

	private void dealWithKernel(Element kernel, String instanceName, String configurationFileName) {
		String cpu = kernel.getAttribute(Output.GLOBAL_TIME);
		String nbRuns = kernel.getAttribute(Output.N_RUNS);
		String vAvg = kernel.getAttribute(Output.N_VAVG);
		String cAvg = kernel.getAttribute(Output.N_CAVG);
		String result = cpu + " " + nbRuns + " " + vAvg + " " + cAvg;
		insert(instanceName, configurationFileName, result);
	}

	private void dealWithFile(File file) {
		if (cnt++ % 200 == 0)
			System.out.println("loading " + file.getName() + " cpt = " + cnt);
		Document document = XMLManager.load(file);
		Kit.control(document != null, () -> "Unloaded document");
		Element resolutions = (Element) document.getElementsByTagName(RESOLUTIONS.toString()).item(0);
		String configurationFileName = Kit.getXMLBaseNameOf(resolutions.getAttribute(Output.CONFIGURATION_FILE_NAME));
		if (kernelExtraction) {
			Element resolution = firstComponentOf(resolutions, RESOLUTION);
			String instanceName = Kit.getXMLBaseNameOf(firstComponentInstanceNameOf(resolution).getAttribute(Output.NAME));
			Element kernel = (Element) document.getElementsByTagName(KERNEL.toString()).item(0);
			dealWithKernel(kernel, instanceName, configurationFileName);
		} else if (seriesExtraction) {
			Element resolution = firstComponentOf(resolutions, RESOLUTION);
			String instanceName = Kit.getXMLBaseNameOf(firstComponentInstanceNameOf(resolution).getAttribute(Output.NAME));
			// + "all" + resolutionList.getLength(),
			dealWithSeries(resolutions, instanceName + "all", configurationFileName);
		} else {
			NodeList resolutionList = document.getElementsByTagName(RESOLUTION.toString());
			for (int i = 0; i < resolutionList.getLength(); i++) {
				Element resolution = (Element) resolutionList.item(i);
				String instanceName = Kit.getXMLBaseNameOf(firstComponentInstanceNameOf(resolution).getAttribute(Output.NAME));
				dealWithInstance(resolution, instanceName, configurationFileName);
			}
		}
	}

	private void dealWith(File file) {
		if (file.isDirectory())
			for (File f : file.listFiles())
				dealWith(f);
		else if (file.isFile()) {
			if (file.length() == 0)
				System.out.println("skipping " + file.getName() + " as it is an empty file");
			else if (!file.getName().toLowerCase().endsWith("xml"))
				System.out.println("skipping " + file.getName() + " as it is not an XML file");
			else
				try {
					dealWithFile(file);
				} catch (Exception e) {
					System.out.println("skipping " + file.getName() + " as a problem occurs " + e);
				}
		}
	}

	private void fillHolesInGlobalMap() {
		String stringForAbsentMethod = repeat(CreateLatexTable.ABSENT, selectedMetrics.size());
		for (Map.Entry<String, Map<String, String>> entry : globalMap.entrySet()) {
			Map<String, String> instanceMap = entry.getValue();
			for (String key : keys)
				if (!instanceMap.containsKey(key))
					instanceMap.put(key, stringForAbsentMethod);
		}
	}

	private String createAlgoHeader(String algo) {
		StringBuilder sb = new StringBuilder();
		for (Metric metric : selectedMetrics) {
			sb.append(algo).append("-").append(Reflector.findFieldName(this, metric)).append(" ");
			// sb.append(algo).append("-").append(metric.attribute).append(" ");
		}
		return sb.toString();
	}

	private String createHeader() {
		StringBuilder sb = new StringBuilder("instance ");
		for (String s : globalMap.get(globalMap.keySet().iterator().next()).keySet())
			sb.append(createAlgoHeader(s));
		return sb.toString();
	}

	private String createLine(String instanceName, Map<String, String> instanceMap) {
		StringBuilder sb = new StringBuilder(instanceName).append(' ');
		for (String s : instanceMap.values())
			sb.append(s).append(' ');
		return sb.toString();
	}

	private void save(String outputFileName) {
		Kit.control(!new File(outputFileName).isDirectory(), () -> outputFileName + " is a directory");
		try {
			PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(new File(outputFileName))));
			out.println(createHeader());
			System.out.println("creating header of " + outputFileName);
			for (Map.Entry<String, Map<String, String>> entry : globalMap.entrySet())
				out.println(createLine(entry.getKey(), entry.getValue()));
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private String repeat(int v, int nbOccurrences) {
		return Stream.generate(() -> v + "").limit(nbOccurrences).collect(Collectors.joining(" "));
	}

	public CreateCampagnDataFile(String inputFileName, String outputFileName, int mode, int metricsMode, boolean mustReachGoal) {
		if (mode == 1 || mode == 3 || mode == 4)
			seriesExtraction = true;
		if (mode == 2)
			kernelExtraction = true;
		// if (mode == 3)
		// extractMedian = true;
		this.mustReachGoal = mustReachGoal;

		if (metricsMode == 1)
			selectMetrics(cpu);
		else if (metricsMode == 2)
			selectMetrics(cpu, mem);
		else if (metricsMode == 3)
			selectMetrics(cpu, mem, nbWrong);
		else if (metricsMode == 4)
			selectMetrics(cpu, mem, nbWrong, nbSolutions);
		else if (metricsMode == 5)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu);
		else if (metricsMode == 6)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, bestBound, bestBoundCpuTime);
		else if (metricsMode == 7)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu, symmetryCpuTime, nbGenerators);
		else if (metricsMode == 8)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu, nbTotalValues, nbRemovedValues, nbAcRemovals);
		else if (metricsMode == 9)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu, nbSingletonTests, nbEffectiveSingletonTests, nbBuiltBranches, sumBranchSizes);
		else if (metricsMode == 10)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu, nbTotalValues, nbRemovedValues, nbAcRemovals, nbRemovedTuples, nbAddedConstraints);
		else if (metricsMode == 11)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu, nbSEliminables, nbREliminables, nbDEliminables, nbIEliminables, nbPEliminables);
		else if (metricsMode == 12)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, nbFilterCalls, avgTableProportion, avgTableSize);
		else if (metricsMode == 13)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, totalInitialSpace, totalReducedSpace, wckMining);
		else if (metricsMode == 14)
			selectMetrics(cpu, mem, nbWrong, nbSolutions, pcpu, nbTotalValues, nbRemovedValues, nbAcRemovals, nbSubRemovals, bestBound, avgSubRemovals,
					nbEffectivePropagations);
		else if (metricsMode == 15)
			selectMetrics(pcpu, mem, nbTotalValues, nbRemovedValues, detectedInconsistency);

		// nbWOS, nbFPs, avgWOs, avgFPs);

		else if (metricsMode == 101)
			selectMetrics(all_cpu);
		else if (metricsMode == 102)
			selectMetrics(all_cpu, all_mem);
		else if (metricsMode == 103)
			selectMetrics(all_wckPREPROCESSING, all_wckSearch, all_nbAssignments);
		else if (metricsMode == 104)
			selectMetrics(all_cpu, all_mem, all_nbAssignments, all_nbSolutions, all_nbRemovedValues, all_nbRemovedTuples, all_nbValidSupports, all_nbInstances);
		else if (metricsMode == 112)
			selectMetrics(all_cpu, all_mem, all_nbAssignments, all_nbSolutions, all_nbFilterCalls, all_avgTableProportion, all_avgTableSize);
		else if (metricsMode == 120)
			selectMetrics(all_cpu, all_mem, all_nbVals, all_nbUnks, all_nbUnksAfterAC, all_nbTests);

		// Output.EXPIRED NB_PREPROCESSING_INCONSISTENCIES };

		error = repeat(CreateLatexTable.ERROR, selectedMetrics.size());

		this.globalMap = new TreeMap<>();
		this.keys = new TreeSet<>();
		dealWith(new File(inputFileName));
		fillHolesInGlobalMap();
		save(outputFileName);
	}

	public static void main(String[] args) {
		if (args.length != 3 && args.length != 4) {
			System.out.println("Usage: " + CreateCampagnDataFile.class.getName() + " <inputFileName | directoryName> <mode> <metricsMode> {<mustReachGoal>}");
			System.out.println("Mode = 0 : extraction for each instance");
			System.out.println("Mode = 1 : extraction for each series (element all)");
			System.out.println("Mode = 2 : extraction for kernels");
			System.out.println("Mode = 3 : extraction for each series (elements all, median)");
			// System.out.println("Mode = 4 : extraction from all elements (transition phase)");
			System.out.println("NB: the name of the file containing the extracted results is built by appending .dat to the string denoting first argument");
		} else
			new CreateCampagnDataFile(args[0], args[0] + ".dat", Integer.parseInt(args[1]), Integer.parseInt(args[2]),
					args.length == 3 ? true : Utilities.toBoolean(args[3]));
	}
}
