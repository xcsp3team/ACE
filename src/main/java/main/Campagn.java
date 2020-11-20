/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package main;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;
import java.util.stream.IntStream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import dashboard.ControlPanel;
import dashboard.Output;
import utility.DocumentHandler;
import utility.Kit;

public class Campagn { // using the cluster

	private static final String VALUE = "value";
	private static final String MIN = "min";
	private static final String MAX = "max";
	private static final String STEP = "step";
	private static final String MIN1 = "min1";
	private static final String MAX1 = "max1";
	private static final String STEP1 = "step1";
	private static final String MIN2 = "min2";
	// private static final String MAX2 = "max2";
	private static final String STEP2 = "step2";
	private static final String DIRECTORY = "directory";
	private static final String RESTRICTION = "restriction";
	private static final String PARAMETERS = "parameters";
	private static final String NB_INSTANCES = "nbInstances";
	private static final String PACKAGE = "package";

	private final static String suffixCommand = ",nodes=1:ppn=1 -m n -- "; // -j oe "; -o /dev/null -- ";

	private final static String[] queueCommands = { "qadd -q short2 -l cput=00:30:00" + suffixCommand, "qadd -q normal2 -l cput=05:00:00" + suffixCommand,
			"qadd -q long2 -l cput=48:00:00" + suffixCommand, "qadd -q short8 -l cput=00:30:00" + suffixCommand,
			"qadd -q normal8 -l cput=05:00:00" + suffixCommand, "qadd -q long8 -l cput=48:00:00" + suffixCommand,
			"qadd -q shortmulti -l cput=00:30:00" + suffixCommand, "qadd -q normalmulti -l cput=05:00:00" + suffixCommand,
			"qadd -q longmulti -l cput=48:00:00" + suffixCommand };

	// private final static String[] queueCommands = { "qadd -q short2 -l cput=00:30:00" + suffixCommand, "qadd -q normal2 -l cput=05:00:00"
	// + suffixCommand, "qadd -q long2 -l cput=48:00:00" + suffixCommand, "qadd -q short_B -l cput=00:30:00"
	// + suffixCommand, "qadd -q normal_B -l cput=05:00:00" + suffixCommand, "qadd -q long_B -l cput=48:00:00"
	// + suffixCommand, "qadd -q shortmulti -l cput=00:30:00" + suffixCommand, "qadd -q normalmulti -l cput=05:00:00"
	// + suffixCommand, "qadd -q longmulti -l cput=48:00:00" + suffixCommand };

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	private String solverCommandPrefix;

	private String defaultSettingsFileName;

	private String selectedInstancesFileName;

	private String settingsVariantsFileName;

	private String directoryName;

	private int queueMode;

	private String[] listOfResultsDirectory;

	private int nLaunchedJobs;

	private String currVariantFileName;

	private boolean currVariantParallel;

	private String getDirectoryNameOf(String suffix) {
		return directoryName + File.separator + suffix;
	}

	private String getDirectoryNameOfContext() {
		return getDirectoryNameOf(Output.CONTEXT_DIRECTORY_NAME);
	}

	private String getDirectoryNameOfConfigurations() {
		return getDirectoryNameOf(Output.CONFIGURATION_DIRECTORY_NAME);
	}

	private String getDirectoryNameOfResults() {
		return getDirectoryNameOf(Output.RESULTS_DIRECTORY_NAME);
	}

	private void saveContext() {
		String directoryNameOfContext = getDirectoryNameOfContext();
		File file = new File(directoryNameOfContext);
		if (!file.exists())
			file.mkdirs();
		else
			Kit.control(file.isDirectory());
		Head.copy(defaultSettingsFileName, directoryNameOfContext + File.separator + defaultSettingsFileName);
		Head.copy(selectedInstancesFileName, directoryNameOfContext + File.separator + selectedInstancesFileName);
		if (settingsVariantsFileName != null)
			Head.copy(settingsVariantsFileName, directoryNameOfContext + File.separator + settingsVariantsFileName);
		String jarName = System.getProperty("java.class.path");
		if (jarName.indexOf(File.pathSeparator) == -1 && jarName.endsWith(".jar")) {
			int index = jarName.lastIndexOf(File.separator);
			index = (index == -1 ? 0 : index + 1);
			Head.copy(jarName, directoryNameOfContext + File.separator + jarName.substring(index));
		}
	}

	private boolean timeForCluster = true;

	public Campagn(String[] args) {
		this.defaultSettingsFileName = args[0];
		this.selectedInstancesFileName = args[1];
		this.settingsVariantsFileName = args[2];
		this.solverCommandPrefix = args[3];
		if (timeForCluster)
			this.solverCommandPrefix = "time " + this.solverCommandPrefix;
		this.queueMode = Integer.parseInt(args[4]);
		Kit.control(queueMode >= 0 && queueMode <= 8, () -> "The queue mode must be set to 0 (short), 1 (normal) or 2 (long)");

		// Arguments.handlerOfConfigurationParametersValues.loadConfigurationFile(defaultConfigurationFileName);
		this.directoryName = (ControlPanel.buildControlPanelFor(defaultSettingsFileName)).settingXml.dirForCampaign;
		Kit.control(!directoryName.trim().equals(""));
		saveContext();
		File file = new File(getDirectoryNameOfConfigurations());
		if (!file.exists())
			file.mkdirs();
		file = new File(getDirectoryNameOfResults());
		if (!file.exists())
			file.mkdirs();

		runVariants();
	}

	// returns the token that follows the one with Output.CONFIGURATION_DIRECTORY_NAME
	private String getInstanceFileNameIn(String command) {
		StringTokenizer st = new StringTokenizer(command);
		while (st.hasMoreTokens())
			if (st.nextToken().contains(Output.CONFIGURATION_DIRECTORY_NAME))
				return st.nextToken();
		return null;
	}

	private boolean isPreviouslyRun(String command) {
		String instanceFileName = getInstanceFileNameIn(command);
		if (instanceFileName != null) {
			String prefix = Output.getOutputFileNamePrefixFrom(instanceFileName, currVariantFileName);
			if (listOfResultsDirectory == null)
				Arrays.sort(listOfResultsDirectory = new File(getDirectoryNameOfResults()).list());
			int index = Arrays.binarySearch(listOfResultsDirectory, prefix);
			Kit.control(index < 0);
			index = -index - 1;
			if (index < listOfResultsDirectory.length && listOfResultsDirectory[index].startsWith(prefix))
				return true; // because already present
		}
		return false;
	}

	private void addJob(String solverCommand) {
		if (!isPreviouslyRun(solverCommand)) {
			nLaunchedJobs++;
			String clusterCommand = queueCommands[queueMode] + solverCommand;
			System.out.println("Job number " + nLaunchedJobs + " : " + clusterCommand);
			try {
				Process p = Runtime.getRuntime().exec(clusterCommand);
				p.waitFor();
				p.exitValue();
				p.destroy();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	private void operateFile(File srcFile) {
		if (!currVariantParallel)
			addJob(solverCommandPrefix + " " + currVariantFileName + " " + srcFile.toString());
		else
			addJob(solverCommandPrefix + " " + (getDirectoryNameOfContext() + File.separator + defaultSettingsFileName) + " " + srcFile.toString() + " "
					+ currVariantFileName);
	}

	private void operateDirectory(File dir, String[] selectedInstances) {
		if (dir.list() == null)
			System.out.println("******************************************** pb with " + dir.getName());
		else
			for (String s : Kit.sort(dir.list()))
				operate(new File(dir, s), selectedInstances);
	}

	private void operate(File file, String[] selectedInstances) {
		if (file.isDirectory())
			operateDirectory(file, selectedInstances);
		else if ((file.getName().toLowerCase().endsWith("xml") || file.getName().toLowerCase().endsWith("bz2") || file.getName().toLowerCase().endsWith("lzma"))
				&& (selectedInstances == null || Arrays.binarySearch(selectedInstances, file.getName()) >= 0))
			operateFile(file);
	}

	private String[] getSelectedInstances(String fileName) {
		if (fileName == null || fileName.length() == 0)
			return null;
		try (BufferedReader in = new BufferedReader(new FileReader(fileName))) {
			List<String> list = new LinkedList<>();
			for (String line = in.readLine(); line != null; line = in.readLine())
				list.add(line.trim());
			return Kit.sort(list.toArray(new String[list.size()]));
		} catch (IOException e) {
			Kit.exit(e);
		}
		return null;
	}

	public void runVariant(String variant, boolean b) {
		currVariantFileName = variant;
		currVariantParallel = b;
		Document document = DocumentHandler.load(selectedInstancesFileName);
		NodeList directoryList = document.getElementsByTagName(DIRECTORY);
		for (int i = 0; i < directoryList.getLength(); i++) {
			Element element = (Element) directoryList.item(i);
			operate(new File(element.getAttribute(VALUE)), getSelectedInstances(element.getAttribute(RESTRICTION)));
		}
		if (!currVariantParallel) {
			// for the moment, only possible with sequential variants
			NodeList parametersList = document.getElementsByTagName(PARAMETERS);
			for (int i = 0; i < parametersList.getLength(); i++) {
				Element elt = (Element) parametersList.item(i);
				String nInstances = elt.getAttribute(NB_INSTANCES);
				String packageName = elt.getAttribute(PACKAGE);
				String value = elt.getAttribute(VALUE);
				// System.out.println(nbInstances + " " + packageName + " " + value);
				int nb = (int) IntStream.range(0, value.length()).filter(j -> value.charAt(j) == '?').count();
				Kit.control(0 <= nb && nb <= 2, () -> "More than two ? in the expression");
				if (nb == 0)
					addJob(solverCommandPrefix + " " + currVariantFileName + " " + nInstances + " " + packageName + " " + value);
				else if (nb == 1) {
					boolean integerRange = elt.getAttribute(MIN).indexOf('.') == -1;
					if (integerRange) {
						int min = Integer.parseInt(elt.getAttribute(MIN));
						int max = Integer.parseInt(elt.getAttribute(MAX));
						int step = elt.getAttribute(STEP).length() == 0 ? 1 : Integer.parseInt(elt.getAttribute(STEP));
						for (int d = min; d <= max; d += step)
							addJob(solverCommandPrefix + " " + currVariantFileName + " " + nInstances + " " + packageName + " " + value.replace("?", d + ""));
					} else {
						double min = Double.parseDouble(elt.getAttribute(MIN));
						double max = Double.parseDouble(elt.getAttribute(MAX));
						double step = elt.getAttribute(STEP).length() == 0 ? 1 : Double.parseDouble(elt.getAttribute(STEP));
						for (double d = min; d <= max; d += step)
							addJob(solverCommandPrefix + " " + currVariantFileName + " " + nInstances + " " + packageName + " " + value.replace("?", d + ""));
					}
				} else if (nb == 2) {
					int pos1 = value.indexOf("?"), pos2 = value.lastIndexOf("?");

					int min1 = Integer.parseInt(elt.getAttribute(MIN1)), min2 = Integer.parseInt(elt.getAttribute(MIN2));
					int max1 = Integer.parseInt(elt.getAttribute(MAX1));// , max2 = Integer.parseInt(elt.getAttribute(MAX2));
					int step1 = Integer.parseInt(elt.getAttribute(STEP1)), step2 = Integer.parseInt(elt.getAttribute(STEP2));
					for (int d1 = min1; d1 <= max1; d1 += step1)
						for (int d2 = min2; d2 < d1; d2 += step2) {
							String v = value.substring(0, pos1) + d1 + " " + value.substring(pos1 + 1, pos2) + d2 + " " + value.substring(pos2 + 1);
							addJob(solverCommandPrefix + " " + currVariantFileName + " " + nInstances + " " + packageName + " " + v);
						}
				}
			}
		}
	}

	public void runVariants() {
		// if (configurationVariantsFileName == null) Kit.copy(defaultConfigurationFileName,
		// getDirectoryNameOfConfigurations() + File.separator + defaultConfigurationFileName);
		String[] sequentialVariants = ResolutionVariants.loadSequentialVariants(defaultSettingsFileName, settingsVariantsFileName,
				getDirectoryNameOfConfigurations() + File.separator);
		for (String sequentialVariant : sequentialVariants)
			runVariant(sequentialVariant, false);
		String[] parallelVariants = ResolutionVariants.loadParallelVariants(settingsVariantsFileName, getDirectoryNameOfConfigurations() + File.separator);
		for (String parallelVariant : parallelVariants)
			runVariant(parallelVariant, true);

		File file = new File(directoryName + File.separator + "synthesis.txt");
		try {
			PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(file, true)));
			out.println("----------------------");
			out.println("  Current time : " + Kit.date());
			out.println("  Command : " + "java abscon.ResolutionCluster " + defaultSettingsFileName + " " + selectedInstancesFileName + " "
					+ settingsVariantsFileName + " " + solverCommandPrefix + " " + queueCommands[queueMode]);
			out.println("  Nb Sequential Variants : " + sequentialVariants.length);
			out.println("  Nb Parallel Variants : " + parallelVariants.length);
			out.println("  Nb Launched Jobs : " + nLaunchedJobs);
			out.println();
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.out.println(" => " + nLaunchedJobs + " jobs launched");
	}

	public static void main(String[] args) throws Exception {
		if (args.length != 5) {
			System.out.println(
					"Usage : java main.Campagn <defaultSettingsFileName> <selectedInstancesFileName> <settingsVariantsFileName> <command>  <queueMode>");
			System.out.println("\n  Queue mode:");
			for (int i = 0; i < queueCommands.length; i++)
				System.out.println("   - queue = " + i + " => " + queueCommands[i]);
			System.out.println("\n  NB: set no to <settingsVariantsFileName> to not take into account variants");
		} else
			new Campagn(args); // [0], args[1], args[2], configurationVariantsFileName,
								// queueMode).run(args[1], configurationVariantsFileName);
	}
}

// private void treat(String completeCommand) {
// System.out.println("command = " + completeCommand);
// try {
// Process p = Runtime.getRuntime().exec(completeCommand);
// BufferedReader in = new BufferedReader(new
// InputStreamReader(p.getInputStream()));
//
// String firstLine = in.readLine();
// String line = firstLine;
// while (line != null)
// line = in.readLine();
// in.close();
//
// p.waitFor();
// int status = p.exitValue();
// p.destroy();
//
// } catch (IOException e) {
// e.printStackTrace();
// } catch (InterruptedException e) {
// e.printStackTrace();
// }
// }
