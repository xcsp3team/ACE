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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xcsp.common.Utilities;

import problem.XCSP3;
import utility.Kit;

/**
 * This class allows us to handle arguments given by the user on the command line. These arguments may concern the
 * problem to solve or more generally the solving process (i.e., options to choose like for example which search
 * heuristics to use).
 * 
 * @author Christophe Lecoutre
 */
public final class Input {

	public static final String SETTINGS = "settings";
	public static final String DEFAULT_SETTINGS = "defaultSettings";
	private static final String OPTION_PREFIX = "-";

	public static final String VARIANT = "variant";
	public static final String VARIANT_PARALLEL = "variantParallel";
	public static final String NAME = "name";
	public static final String MODIFICATION = "modification";
	public static final String PATH = "path";
	public static final String ATTRIBUTE = "attribute";
	public static final String VALUE = "value";
	public static final String MIN = "min";
	public static final String MAX = "max";
	public static final String STEP = "step";
	public static final String SEED = "seed";

	/**
	 * All user arguments given on the command line
	 */
	public static String[] args;

	/**
	 * The user arguments given on the command that concern the problem (instance). For XCSP3 instances, the array only
	 * contains the XCSP3 filename.
	 */
	public static String[] argsForProblem;

	/**
	 * The user arguments given on the command that concern the control panel (i.e., the solving process)
	 */
	public final static Map<String, String> argsForSolving = new HashMap<>(256);

	/**
	 * Indicates if a portfolio is used, i.e., various solving processes will be running in parallel
	 */
	public static boolean portfolio;

	/**
	 * The filename for controls, if such a file is given by the user on the command line
	 */
	public static String controlFilename;

	/**
	 * The name of the package corresponding to the problem to be loaded. If an XCSP3 instance is given by the user on
	 * the command line, the package is problem.XCSP3.
	 */
	public static String problemName;

	/**
	 * The number of instances to be solved. Usually, this is 1.
	 */
	public static int nInstancesToSolve = 1;

	/**
	 * Returns the last argument passed by the user on the command line
	 * 
	 * @return the last argument passed by the user on the command line
	 */
	public static String lastArgument() {
		return args[args.length - 1];
	}

	private static int setNInstancesToSolveFrom(String token) {
		if (token.toLowerCase().equals(Control.UserSettings.ALL)) {
			nInstancesToSolve = Integer.MAX_VALUE;
			return 1;
		}
		if (Utilities.isInteger(token)) {
			int number = Utilities.toInteger(token);
			control(number == -1 || number > 0, () -> "invalid number of instances");
			nInstancesToSolve = number == -1 ? Integer.MAX_VALUE : number; // -1 stands for all
			return 1;
		}
		nInstancesToSolve = 1;
		return 0;
	}

	/**
	 * Sets the arguments passed by the user on the command line
	 * 
	 * @param args
	 *            arguments given by the sued on the command line
	 */
	public static void loadArguments(String... args) {
		Input.args = args = Stream.of(args).filter(s -> s.length() > 0).toArray(String[]::new); // cleaning and storing
																								// args
		control(args.length > 0);
		Input.portfolio = Kit.isXMLFileWithRoot(lastArgument(), VARIANT_PARALLEL);
		int cursor = 0;
		Input.controlFilename = Kit.isXMLFileWithRoot(args[cursor], SETTINGS) ? args[cursor++] : DEFAULT_SETTINGS;
		// control of this file performed later
		cursor += setNInstancesToSolveFrom(args[cursor]);
		control(!portfolio || nInstancesToSolve == 1);
		control(cursor < args.length && !args[cursor].startsWith(OPTION_PREFIX), () -> "The package name or (for XCSP) the instance file name is missing.");
		Input.problemName = args[cursor].endsWith(".xml") || args[cursor].endsWith(".lzma") ? XCSP3.class.getName() : args[cursor++];
		List<String> list = new ArrayList<>();
		while (cursor < args.length && (!args[cursor].startsWith(OPTION_PREFIX) || Utilities.isInteger(args[cursor])))
			list.add(args[cursor++]);
		Input.argsForProblem = list.toArray(new String[list.size()]);
		// now, we look for solving options
		Input.argsForSolving.clear();
		Set<String> setOfUserKeys = new HashSet<>();
		for (; cursor < args.length; cursor++) {
			String arg = args[cursor];
			control(arg.startsWith(OPTION_PREFIX), () -> arg + " is not put at the right position");
			int equalPosition = arg.indexOf('=');
			String key = equalPosition > 1 ? arg.substring(1, equalPosition) : arg.substring(1);
			String value = equalPosition > 1 ? (equalPosition == arg.length() - 1 ? "" : arg.substring(equalPosition + 1)) : "true";
			if (setOfUserKeys.contains(key))
				control(Input.argsForSolving.get(key).contentEquals(value), () -> "The configuration key " + key
						+ " appears several times with different values: " + value + " vs " + Input.argsForSolving.get(key));
			else
				Input.argsForSolving.put(key, value);
			setOfUserKeys.add(key);
			// TODO control validity of key-value
		}
	}

	public static String[] loadSequentialVariants(String controlFilename, String controlVariantsFilename, String prefix) {
		List<String> list = new ArrayList<>();
		Document document = Kit.load(controlVariantsFilename);
		NodeList variants = document.getElementsByTagName(VARIANT);
		for (int i = 0; i < variants.getLength(); i++) {
			Element variant = (Element) variants.item(i);
			Element parent = (Element) variant.getParentNode();
			if (!document.getDocumentElement().getTagName().equals(VARIANT_PARALLEL) && parent.getTagName().equals(VARIANT_PARALLEL))
				continue;
			Document docVariant = Kit.load(controlFilename);
			String docFilename = prefix + (parent.getTagName().equals(VARIANT_PARALLEL) ? parent.getAttribute(NAME) + "_" : "") + variant.getAttribute(NAME)
					+ ".xml";
			NodeList modifications = variant.getElementsByTagName(MODIFICATION);
			int nModifications = modifications.getLength();
			boolean iteration = nModifications > 0 && !((Element) modifications.item(nModifications - 1)).getAttribute(MIN).equals("");
			int limit = nModifications - (iteration ? 1 : 0);
			for (int j = 0; j < limit; j++) {
				Element modificationElement = (Element) modifications.item(j);
				String path = modificationElement.getAttribute(PATH);
				String attributeName = modificationElement.getAttribute(ATTRIBUTE);
				String attributeValue = modificationElement.getAttribute(VALUE);
				Kit.modify(docVariant, path, attributeName, attributeValue);
			}
			if (iteration) {
				Element modification = (Element) modifications.item(nModifications - 1);
				String path = modification.getAttribute(PATH);
				control(path.equals(SEED));
				String attributeName = modification.getAttribute(ATTRIBUTE);
				int min = Integer.parseInt(modification.getAttribute(MIN)), max = Integer.parseInt(modification.getAttribute(MAX)),
						step = Integer.parseInt(modification.getAttribute(STEP));
				String basis = docFilename.substring(0, docFilename.lastIndexOf(".xml"));
				for (int cnt = min; cnt <= max; cnt += step) {
					Kit.modify(docVariant, path, attributeName, cnt + "");
					list.add(Utilities.save(docVariant, basis + cnt + ".xml"));
				}
			} else
				list.add(Utilities.save(docVariant, docFilename));
		}
		return list.toArray(new String[list.size()]);
	}

	public static String[] loadParallelVariants(String controlVariantsFilename, String prefix) {
		List<String> list = new ArrayList<>();
		Document document = Kit.load(controlVariantsFilename);
		if (!document.getDocumentElement().getTagName().equals(VARIANT_PARALLEL)) {
			NodeList nodeList = document.getElementsByTagName(VARIANT_PARALLEL);
			for (int i = 0; i < nodeList.getLength(); i++) {
				Document docVariant = Kit.createNewDocument();
				Element element = (Element) docVariant.importNode(nodeList.item(i), true);
				docVariant.appendChild(element);
				list.add(Utilities.save(docVariant, prefix + element.getAttribute(NAME) + ".xml"));
			}
		}
		return list.toArray(new String[list.size()]);
	}

}
