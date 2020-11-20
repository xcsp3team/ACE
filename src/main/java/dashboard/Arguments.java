/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package dashboard;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import main.ResolutionVariants;
import utility.DocumentHandler;
import utility.Kit;
import xcsp3.XCSP3;

/**
 * This class allows us to handle arguments given by the user on the command line.
 */
public final class Arguments {

	private static final String SETTING_VALUE_PREFIX = "-";

	public static final String DEFAULT_PROBLEMS_PREFIX = "problems";

	/** User arguments given on the command line */
	public static String[] args;

	/** User arguments given on the command for the problem (instance) */
	public static String[] argsForPb;

	/** User arguments given on the command for the control panel */
	public final static Map<String, String> argsForCp = new HashMap<>(256);

	public static boolean multiThreads;

	public static String userSettingsFilename;

	public static String problemPackageName;

	// TODO to put elsewhere ? because can be specific to each resolution object ?
	public static int nInstancesToSolve = 1;

	public static String lastArgument() {
		return args[args.length - 1];
	}

	private static int nInstancesToSolveFrom(String token) {
		try {
			if (token.toLowerCase().equals(ControlPanel.ALL)) {
				nInstancesToSolve = Integer.MAX_VALUE;
				return 1;
			} else if (Utilities.isInteger(token)) {
				int number = Integer.parseInt(token);
				Kit.control(number == -1 || number > 0, () -> "invalid number of instances");
				nInstancesToSolve = number == -1 ? Integer.MAX_VALUE : number;
				return 1;
			} else {
				nInstancesToSolve = 1;
				return 0;
			}
		} catch (NumberFormatException e) {
			return (Integer) Kit.exit("The number of instances to be solved must be a positive  integer, -1 or all (" + token + " is not valid )", e);
		}
	}

	/**
	 * Sets the arguments passed by the user in command line.
	 */
	public static void loadArguments(String... args) {
		argsForCp.clear();
		args = Stream.of(args).filter(s -> s.length() > 0).toArray(String[]::new);
		Kit.control(args.length > 0);
		Arguments.args = args;
		multiThreads = DocumentHandler.isXMLFileWithRoot(args[args.length - 1], ResolutionVariants.VARIANT_PARALLEL);
		int cursor = 0;
		userSettingsFilename = DocumentHandler.isXMLFileWithRoot(args[cursor], ControlPanel.CONFIGURATION) ? args[cursor++] : ControlPanel.DEFAULT_CONFIGURATION;
		// control of this file performed later
		cursor += nInstancesToSolveFrom(args[cursor]);
		Kit.control(!multiThreads || nInstancesToSolve == 1);
		Kit.control(cursor < args.length && !args[cursor].startsWith(SETTING_VALUE_PREFIX),
				() -> "The package name or (for XCSP) the instance file name is missing.");
		problemPackageName = args[cursor].endsWith(".xml") || args[cursor].endsWith(".lzma") ? XCSP3.class.getName() : args[cursor++];
		List<String> list = new ArrayList<>();
		while (cursor < args.length && (!args[cursor].startsWith(SETTING_VALUE_PREFIX) || Utilities.isInteger(args[cursor])))
			list.add(args[cursor++]);
		argsForPb = list.toArray(new String[list.size()]);
		// now, look For Configuration Parameters
		Set<String> setOfUserKeys = new HashSet<>();
		for (; cursor < args.length; cursor++) {
			String arg = args[cursor];
			Kit.control(arg.startsWith(SETTING_VALUE_PREFIX), () -> arg + " is not put at the right position");
			int equalPosition = arg.indexOf('=');
			String key = equalPosition > 1 ? arg.substring(1, equalPosition) : arg.substring(1);
			String value = equalPosition > 1 ? (equalPosition == arg.length() - 1 ? "" : arg.substring(equalPosition + 1)) : "true";
			Kit.control(!setOfUserKeys.contains(key), () -> "The configuration key " + key + " appears several times.");
			argsForCp.put(key, value);
			setOfUserKeys.add(key);
			// TODO control validity of key-value
		}
	}

	public static void loadArguments(String[] args, String... otherArgs) {
		loadArguments(Stream.concat(Arrays.stream(args), Arrays.stream(otherArgs)).toArray(String[]::new));
	}
}
