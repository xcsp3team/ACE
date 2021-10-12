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

import static java.util.stream.Collectors.joining;
import static org.xcsp.common.Constants.MINUS_INFINITY;
import static org.xcsp.common.Constants.PLUS_INFINITY;
import static org.xcsp.common.Constants.PLUS_INFINITY_INT;
import static problem.Problem.SymmetryBreaking.NO;
import static utility.Kit.control;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.util.logging.Level;
import java.util.stream.Stream;
import java.util.zip.Deflater;

import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xcsp.common.Constants;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeCtr;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.ConstraintExtension.Extension;
import constraints.extension.structures.Bits;
import constraints.extension.structures.Matrix.Matrix3D;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstGE;
import heuristics.HeuristicRevisions;
import heuristics.HeuristicRevisions.HeuristicRevisionsDynamic.Dom;
import heuristics.HeuristicValues;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.SingletonStrategy;
import heuristics.HeuristicVariablesDynamic.Wdeg;
import heuristics.HeuristicVariablesDynamic.WdegVariant.ConstraintWeighting;
import interfaces.Tags.TagExperimental;
import learning.IpsReasoner.LearningIps;
import learning.NogoodReasoner.LearningNogood;
import main.Head;
import main.HeadExtraction;
import main.HeadExtraction.Extraction;
import optimization.ObjectiveVariable;
import optimization.Optimizer;
import optimization.Optimizer.OptimizationStrategy;
import problem.Problem.SymmetryBreaking;
import propagation.AC;
import propagation.Reviser;
import propagation.Reviser.Reviser3;
import solver.Restarter.RestartMeasure;
import solver.Restarter.RestarterLNS.HeuristicFreezing.Rand;
import solver.Solver;
import solver.Solver.Branching;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

/**
 * This class allows us to manage all options concerning the problem (typically, the way to represent it) and the solver
 * (typically, the way to conduct search).
 * 
 * @author Christophe Lecoutre
 */
public final class Control {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	/**
	 * Value to be used as priority level for hiding an option (when saving the control file)
	 */
	private static final int HIDDEN = 4;

	public static void main(String[] args) {
		Integer maximumPriority = args.length != 2 ? null : Utilities.toInteger(args[1]);
		if (args.length != 2 || maximumPriority == null || maximumPriority < 1 || maximumPriority > 3) {
			System.out.println("\tTool used to generate a default option settings file.");
			System.out.println("\tUsage : " + Control.class.getName() + " <outputFileName> <maximumPriority>");
			System.out.println("\n\toutputFileName : name of the generated option settings file.");
			System.out.println("\n\tmaximumPriority : only parameters with a priority value lower than this number (between 1 and 3) are generated");
		} else {
			new File(Kit.getPathOf(args[0])).mkdirs();
			Control control = new Control(null);
			control.save(args[0] + (args[0].endsWith(".xml") ? "" : ".xml"), maximumPriority);
		}
	}

	/**********************************************************************************************
	 * Fields and methods
	 *********************************************************************************************/

	/**
	 * The various options, from different groups, stored in a unique list
	 */
	private final List<Option<?>> options;

	/**
	 * The object dealing with options given by the user, either on the command line or by means of an XML control file
	 */
	public final UserSettings userSettings;

	public final SettingGeneral general;

	public final SettingProblem problem;

	public final SettingVars variables;

	public final SettingOptimization optimization;

	public final SettingCtrs constraints;

	public final SettingExtension extension;

	public final SettingIntension intension;

	public final SettingGlobal global;

	public final SettingPropagation propagation;

	public final SettingShaving shaving;

	public final SettingLearning learning;

	public final SettingSolving solving;

	public final SettingRestarts restarts;

	public final SettingLNS lns;

	public final SettingVarh varh;

	public final SettingValh valh;

	public final SettingRevh revh;

	public final SettingExtraction extraction;

	public final SettingExperimental experimental;

	public Control(String controlFilename) {
		this.options = new ArrayList<>();
		this.userSettings = new UserSettings(controlFilename);

		this.general = new SettingGeneral();

		this.problem = new SettingProblem();
		this.variables = new SettingVars();
		this.optimization = new SettingOptimization();

		this.constraints = new SettingCtrs();
		this.extension = new SettingExtension();
		this.intension = new SettingIntension();
		this.global = new SettingGlobal();

		this.propagation = new SettingPropagation();
		this.shaving = new SettingShaving();
		this.learning = new SettingLearning();

		this.solving = new SettingSolving();
		this.restarts = new SettingRestarts();
		this.lns = new SettingLNS();

		this.extraction = new SettingExtraction();

		this.revh = new SettingRevh();
		this.varh = new SettingVarh();
		this.valh = new SettingValh();

		this.experimental = new SettingExperimental();

		general.verbose = general.verbose < 1 && general.trace.length() > 0 ? 1 : general.verbose;
		control(0 <= general.verbose && general.verbose <= 3, () -> "Verbose must be in 0..3");
		Kit.log.setLevel(general.verbose == 0 ? Level.CONFIG : general.verbose == 1 ? Level.FINE : general.verbose == 2 ? Level.FINER : Level.FINEST);
		control(0 <= lns.pFreeze && lns.pFreeze < 100, () -> "percentageOfVariablesToFreeze should be between 0 and 100 (excluded)");
		control(learning.nogood == LearningNogood.NO || learning.nogood == LearningNogood.RST, "other values currently not available");
		control(optimization.lb <= optimization.ub);
		controlKeys();
		if (general.exceptionsVisible)
			org.xcsp.modeler.Compiler.ev = true;
		if (general.noPrintColors)
			Kit.useColors = false;
		// if (framework == TypeFramework.MAXCSP) optimization.lb = 0L;
	}

	public void framework(Optimizer optimizer) {
		if (optimizer != null) {
			if (general.solLimit == -1)
				general.solLimit = PLUS_INFINITY; // default value for COP (in order to find an optimum)
			if (optimizer.ctr instanceof ObjectiveVariable || optimizer.ctr instanceof MaximumCstLE || optimizer.ctr instanceof MinimumCstGE)
				restarts.restartAfterSolution = true;
		} else {
			if (general.solLimit == -1)
				general.solLimit = 1; // default value for CSP
		}
	}

	private void controlKeys() {
		Stream<String> keys = Input.argsForSolving.keySet().stream();
		String k = keys.filter(key -> options.stream().noneMatch(s -> s.key().equals(key) || s.shortcut.equals(key))).findFirst().orElse(null);
		control(k == null, () -> "The parameter " + k + " is unknown");
	}

	private void save(String outputFilename, int maximumPriority) {
		Document document = Kit.createNewDocument();
		Node root = document.appendChild(document.createElement(Input.SETTINGS));
		for (Option<?> option : options)
			if (option.priority <= maximumPriority) {
				NodeList list = document.getElementsByTagName(option.tag);
				if (list.getLength() == 0) {
					root.appendChild(document.createElement(option.tag));
					list = document.getElementsByTagName(option.tag);
				}
				control(list.getLength() == 1);
				Object value = option.defaultValue;
				if (value instanceof Number) {
					Number n = (Number) option.defaultValue;
					value = n.longValue() == Long.MIN_VALUE || n.intValue() == Integer.MIN_VALUE ? "min"
							: n.longValue() == Long.MAX_VALUE || n.intValue() == Integer.MAX_VALUE ? "max" : value;
				}
				((Element) list.item(0)).setAttribute(option.attribute.trim(), value.toString());
			}
		Utilities.save(document, outputFilename);
	}

	public void display() {
		try (Scanner scanner1 = new Scanner(Head.class.getResource("/displayPart1.txt").openStream());
				Scanner scanner2 = new Scanner(Head.class.getResourceAsStream("/displayPart2.txt"));) {
			while (scanner1.hasNext())
				System.out.println(scanner1.nextLine());
			String tag = null;
			for (Option<?> option : options)
				if (option.priority != HIDDEN)
					System.out.print((!option.tag.equals(tag) ? "\n  " + (tag = option.tag) + "\n" : "") + option);
			System.out.println();
			while (scanner2.hasNext())
				System.out.println(scanner2.nextLine());
		} catch (Exception e) {
			Kit.exit("Error while loading display files", e);
		}
	}

	/**********************************************************************************************
	 ***** Inner classes for options
	 *********************************************************************************************/

	private class Option<T> {

		protected final String tag, attribute, shortcut;

		protected final T defaultValue;

		protected T value;

		private final String description;

		private final int priority;

		private Class<?> root;

		private final String[] discarded = Stream.of(Extraction.MAX_CSP.name(), Extraction.INC.name(), Extraction.INC_FIRST.name()).sorted()
				.toArray(String[]::new);

		private T getValue(String shortcut, String tag, String attribute, T defaultValue) {
			if (defaultValue == null)
				return null;
			Class<T> clazz = (Class<T>) defaultValue.getClass();
			if (defaultValue instanceof Integer)
				return clazz.cast(userSettings.intFor(shortcut, tag, attribute, (Integer) defaultValue));
			if (defaultValue instanceof Long)
				return clazz.cast(userSettings.longFor(shortcut, tag, attribute, (Long) defaultValue));
			if (defaultValue instanceof Double)
				return clazz.cast(userSettings.doubleFor(shortcut, tag, attribute, (Double) defaultValue));
			if (defaultValue instanceof Boolean)
				return clazz.cast(userSettings.booleanFor(shortcut, tag, attribute, (Boolean) defaultValue));
			if (defaultValue instanceof String)
				return clazz.cast(userSettings.stringFor(shortcut, tag, attribute, defaultValue));
			if (defaultValue instanceof Enum<?>) {
				// Class<? extends Enum<?>> cl = (Class<? extends Enum<?>>) defaultValue.getClass();
				// Class<T> c = (Class<T>) defaultValue.getClass();
				// String s=""; return Enum.valueOf(cl, s.toUpperCase());
			}
			return null;
		}

		private Option(String tag, String attribute, String shortcut, T defaultValue, String description, int... priority) {
			this.tag = tag;
			this.attribute = attribute;
			this.shortcut = shortcut == null || shortcut.length() == 0 ? attribute : shortcut;
			this.defaultValue = defaultValue;
			this.value = getValue(this.shortcut, tag, attribute, defaultValue);
			this.description = description;
			this.priority = priority.length == 0 ? 1 : priority.length == 1 ? priority[0] : (Integer) Kit.exit("Only zero or one priority value expected");
		}

		private Option(String tag, String attribute, String shortcut, String defaultValue, Class<?> root, String description, int... priority) {
			this(tag, attribute, shortcut, (T) defaultValue, description, priority);
			this.root = root;
			control(1 <= this.priority && this.priority <= 4 && tag != null && attribute != null && defaultValue != null && value != null);
		}

		protected String key() {
			return tag + "/" + attribute; // (attributeAmbiguity ? tag + "/" : "") + attribute;
		}

		@Override
		public String toString() {
			String s = new String();
			s += "    -" + key() + (shortcut != null ? " -" + shortcut : "") + "\n";
			s += "\t" + (description == null || description.length() == 0 ? "Description is missing..." : description) + "\n";
			s += "\tDefault value is : " + (defaultValue instanceof String && ((String) defaultValue).length() == 0 ? "\"\" (empty string)" : defaultValue)
					+ "\n";
			if (root != null)
				s += "\tPossible values: " + Stream.of(Reflector.searchClassesInheritingFrom(root)).filter(c -> !(TagExperimental.class.isAssignableFrom(c)))
						.map(c -> c.getSimpleName()).collect(joining(" ")) + "\n";
			if (value instanceof Enum<?>)
				s += "\tPossible values: " + Stream.of(value.getClass().getDeclaredFields())
						.filter(f -> f.isEnumConstant() && Arrays.binarySearch(discarded, f.getName()) < 0).map(f -> f.getName()).collect(joining(" ")) + "\n";
			return s;
		}
	}

	private final class OptionEnum<T extends Enum<T>> extends Option<T> {

		private OptionEnum(String tag, String attribute, String shortcut, T defaultValue, String description, int... priority) {
			super(tag, attribute, shortcut, defaultValue, description, priority);
			this.value = Enum.valueOf((Class<T>) defaultValue.getClass(), userSettings.stringFor(this.shortcut, tag, attribute, defaultValue).toUpperCase());
		}
	}

	/**********************************************************************************************
	 * Groups of options
	 *********************************************************************************************/

	private class SettingGroup {

		private <T> T add(Option<T> option) {
			control(option.shortcut != null, () -> "A shortcut must be given");
			for (Option<?> opt : options) {
				control(!option.shortcut.equals(opt.shortcut), () -> opt.key() + " and " + option.key() + " with the same shortcut " + option.shortcut);
				control(!opt.key().equals(option.key()), () -> "The parameters " + opt.key() + " and " + option.key() + " with the same value");
			}
			options.add(option);
			return option.value;
		}

		private String tag() {
			control(getClass().getSimpleName().startsWith("Setting"));
			return getClass().getSimpleName().substring(7);
		}

		protected int addI(String attribute, String shortcut, int defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority));
		}

		protected long addL(String attribute, String shortcut, long defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority));
		}

		protected double addD(String attribute, String shortcut, double defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority));
		}

		protected boolean addB(String attribute, String shortcut, boolean defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority));
		}

		protected String addS(String attribute, String shortcut, String defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority)).trim();
		}

		protected String addS(String attribute, String shortcut, Class<?> defaultValue, Class<?> root, String description, int... priority) {
			String df = defaultValue == null ? "" : defaultValue.getName().substring(defaultValue.getName().lastIndexOf(".") + 1);
			root = root == null ? Reflector.getLastButOneSuperclassOf(defaultValue) : root;
			return add(new Option<String>(tag(), attribute, shortcut, df, root, description, priority)).trim();
		}

		protected <T extends Enum<T>> T addE(String attribute, String shortcut, T defaultValue, String description, int... priority) {
			return add(new OptionEnum<>(tag(), attribute, shortcut, defaultValue, description, priority));
		}
	}

	public class SettingGeneral extends SettingGroup {
		String s_verbose = "\n\t0 : only some global statistics are listed ;" + "\n\t1 : in addition, solutions are  shown ;"
				+ "\n\t2 : in addition, additionnal information about the problem instance to be solved is given ;"
				+ "\n\t3 : in addition, for each constraint, allowed or unallowed tuples are displayed.";

		// below, -1 when not initialized
		public long solLimit = addL("solLimit", "s", -1, "The limit on the number of found solutions before stopping; for no limit, use -s=all");
		public final long timeout = addL("timeout", "t", PLUS_INFINITY, "The limit in milliseconds before stopping; seconds can be indicated as in -t=10s");
		public final String discardClasses = addS("discardClasses", "dc", "", "XCSP3 classes (tags) to be discarded (comma as separator)");
		public final String campaignDir = addS("campaignDir", "cd", "", "Name of a campaign directory where results (XML files) are stored.");
		public final String trace = addS("trace", "trace", "", "Displays a trace (with possible depth control as eg -trace=10-20");
		public final int jsonLimit = addI("jsonLimit", "jl", 1000, "The limit on the number of variables for displaying solutions in JSON");
		public final boolean jsonAux = addB("jsonAux", "ja", false, "Take auxiliary variables when displaying solutions in JSON");
		public final boolean xmlCompact = addB("xmlCompact", "xc", true, "Compress values when displaying solutions in XML");
		public final boolean xmlEachSolution = addB("xmlEachSolution", "xe", false, "During search, display all found solutions in XML");
		public final boolean noPrintColors = addB("noPrintColors", "npc", false, "Don't use special color characters in the terminal");
		public final boolean exceptionsVisible = addB("exceptionsVisible", "ev", false, "Makes exceptions visible.");
		public final boolean enableAnnotations = addB("enableAnnotations", "ea", false, "Enables annotations (currently, mainly concerns priority variables).");
		public final int satisfactionLimit = addI("satisfactionLimit", "satl", PLUS_INFINITY_INT, "Converting the objective into a constraint with this limit");
		public final long seed = addL("seed", "seed", 0, "The seed that can be used for some random-based methods.");
		public int verbose = addI("verbose", "v", 0, "Verbosity level (value between 0 and 3)" + s_verbose);
	}

	public class SettingProblem extends SettingGroup {
		public final String data = addS("data", "", "", "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName());
		public final String variant = addS("variant", "", "", "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName());
		public final boolean shareBits = addB("shareBits", "", false, "Trying to save space by sharing bit vectors.");
		public final SymmetryBreaking symmetryBreaking = addE("symmetryBreaking", "sb", NO, "Symmetry-breaking method (requires Saucy to be installed");
	}

	public class SettingVars extends SettingGroup {
		String s_sel = "Allows us to give a list of variable that will form the subproblem to be solved."
				+ "\n\tThis list is composed of a sequence of tokens separated by commas (no whitespace)."
				+ "\n\tEach token is a variable id a variable number or an interval of the form i..j with i and j integers."
				+ "\n\tFor example, -sel=2..10,31,-4 will denote the list 2 3 5 6 7 8 9 10 31." + "\n\tThis is only valid for a XCSP instance.";
		String s_ins = "Allows us to give an instantiation of variables for the problem to be solved."
				+ "\n\tThis instantiation is given under the form vars:values."
				+ "\n\tvars is a sequence of variable ids or numbers separated by commas (no whitespace)."
				+ "\n\tvalues is a sequence of integers (the values for variables) separated by commas (no whitespace)."
				+ "\n\tFor example, -ins=x2,x4,x9:1,11,4 will denote the instantiation {x2=1,x4=11,x9=4}.";
		String s_pr1 = "Allows us to give a list of variables that will become strict priority variables (to be used by the variable ordering heuristic)."
				+ "\n\tThis list is composed of a sequence of strings (ids of variables) or integers (numbers of variables) separated by commas (no whitespace)."
				+ "\n\tFor example, -pr1=2,8,1,10 will denote the list 2 8 1 10.";
		String s_pr2 = "Allows us to give a list of variables that will become (non strict) priority variables."
				+ "\n\tThis list is composed of a sequence of tokens separated by commas (no whitespace)."
				+ "\n\tEach token is variable id, a variable number (integer) or an interval of the form i..j with i and j integers.."
				+ "\n\tFor example, -pr2=2..10,31,-4 will denote the list 2 3 5 6 7 8 9 10 31.";

		protected final String selection = addS("selection", "sel", "", s_sel);
		protected final String instantiation = addS("instantiation", "ins", "", s_ins);
		protected final String priority1 = addS("priority1", "pr1", "", s_pr1);
		protected final String priority2 = addS("priority2", "pr2", "", s_pr2);
		public final boolean reduceIsolated = addB("reduceIsolated", "riv", true, "Arbitrary keeping a single value in the domain of isolated variables");

		private Object[] readSelectionList(String s) {
			if (s == null || s.trim().length() == 0)
				return new Object[0];
			String msg = "Badly formed list. For example, you cannot mix ids and numbers of variables in the same list.";
			Set<Object> set = new HashSet<>();
			for (String token : s.split(",")) {
				if (token.contains("..")) {
					control(token.matches("-?\\d+\\.\\.\\d+"), () -> msg + " Pb with " + token);
					control(set.isEmpty() || set.iterator().next() instanceof Integer, () -> msg);
					int[] t = Utilities.toIntegers(token.split("\\.\\."));
					for (int num = Math.abs(t[0]); num <= t[1]; num++)
						if (t[0] >= 0)
							set.add(num);
						else
							set.remove(num);
				} else {
					Integer num = Utilities.toInteger(token);
					if (num != null) {
						control(set.isEmpty() || set.iterator().next() instanceof Integer, () -> msg);
						if (num >= 0)
							set.add(num);
						else
							set.remove(-num);
					} else {
						control(set.isEmpty() || set.iterator().next() instanceof String, () -> msg);
						set.add(token); // id
					}
				}
			}
			return set.stream().sorted().toArray();
		}

		private Object splitSelection(boolean left) {
			if (instantiation.trim().length() == 0)
				return left ? new Object[0] : new int[0];
			String[] t = instantiation.trim().split(":");
			control(t.length == 2, () -> instantiation);
			return left ? readSelectionList(t[0]) : Utilities.toIntegers(t[1].split(","));
		}

		private Object[] controlAndFinalizeVariablesLists(Object[] priority1Vars, Object[] priority2Vars) {
			// Selected variables are only valid for XCSP ; control about instantiatedVars and instantiatedVals is made
			// in reduceDomainsFromUserInstantiation of Problem
			Object[] t = Stream.concat(Stream.concat(Stream.of(instantiatedVars), Stream.of(priority1Vars)), Stream.of(priority2Vars)).toArray(Object[]::new);
			if (t.length > 0) {
				control(Stream.of(t).distinct().count() == t.length, () -> "Two variables are identical in your lists (-sel -pr1 -pr2)");
				control(selectedVars.length == 0 || Stream.of(t).allMatch(o -> Arrays.binarySearch(selectedVars, o) >= 0),
						() -> "One variable present in one of your list -ins -pr1 or -pr2 is not present in your selection (-sel).");
			}
			return t;
		}

		// either nums of selected variables or ids of selected variables
		public final Object[] selectedVars = readSelectionList(selection);

		// either nums of instantiated variables or ids of instantiated variables
		public final Object[] instantiatedVars = (Object[]) splitSelection(true);

		public final int[] instantiatedVals = (int[]) splitSelection(false);

		private final Object[] priority1Vars = readSelectionList(priority1), priority2Vars = readSelectionList(priority2);

		public final Object[] priorityVars = controlAndFinalizeVariablesLists(priority1Vars, priority2Vars);

		public final int nStrictPriorityVars = instantiatedVars.length + priority1Vars.length;
	}

	public class SettingOptimization extends SettingGroup {
		public long lb = addL("lb", "lb", MINUS_INFINITY, "initial lower bound");
		public long ub = addL("ub", "ub", PLUS_INFINITY, "initial upper bound");
		public final OptimizationStrategy strategy = addE("strategy", "os", OptimizationStrategy.DECREASING, "optimization strategy");
	}

	public class SettingCtrs extends SettingGroup {
		public final boolean preserve1 = addB("preserve1", "pc1", true, "Must we keep unary constraints (instead of filtering them straight)");
		public final TypeCtr ignoredType = Types.valueOf(TypeCtr.class, addS("ignoreType", "", "", "Dicard all constraints of this type"));
		public final int ignoreArity = addI("ignoreArity", "", -1, "Discard all constraints of this arity");
		public final int positionsLb = addI("positionsLb", "poslb", 3, "Minimal arity to build the array positions");
		public final int positionsUb = addI("positionsUb", "posub", 10000, "Maximal number of variables to build the array positions");
	}

	public class SettingExtension extends SettingGroup {
		public final Extension positive = addE("positive", "", Extension.CT, "Algorithm for (non-binary) positive table constraints");
		public final Extension negative = addE("negative", "", Extension.V, "Algorithm for (non-binary) negative table constraint");
		public final boolean generic2 = addB("generic2", "", true, "Should we use a generic filtering scheme for binary table constraints?");
		public final String structureClass2 = addS("structureClass2", "sc2", Bits.class, null, "Structures to be used for binary table constraints");
		public final String structureClass3 = addS("structureClass3", "sc3", Matrix3D.class, null, "Structures to be used for ternary table constraints");
		public final int arityLimitToPositive = addI("arityLimitToPositive", "alp", -1, "Limit on arity for converting negative table constraints to positive");
		public final int arityLimitToNegative = addI("arityLimitToNegative", "aln", -1, "Limit on arity for converting positive table constraints to negative");
		public final int variant = addI("variant", "extv", 0, "Variant to be used for some algorithms (e.g., VA or CMDD)");
		public final boolean decremental = addB("decremental", "extd", true, "Should we use a decremental mode for some algorithms (e.g., STR2, CT or CMDD)");

		public boolean reverse(int arity, boolean positive) {
			return (positive && arity <= arityLimitToNegative) || (!positive && arity <= arityLimitToPositive);
		}
	}

	public class SettingIntension extends SettingGroup {
		public final int decompose = addI("decompose", "di", 1, "0: no decomposition, 1: conditional decomposition, 2: forced decompostion");
		public final boolean toExtension1 = addB("toExtension1", "ie1", true, "Must we convert unary intension constraints to extension?");
		public final int arityLimitToExtension = addI("arityLimitToExtension", "ale", 0, "Limit on arity for possibly converting to extension");
		public final int spaceLimitToExtension = addI("spaceLimitToExtension", "sle", 20, "Limit on space for possibly converting to extension");
		// The following options determine whether special forms of intension constraints must be recognized/intercepted
		public final boolean recognizePrimitive2 = addB("recognizePrimitive2", "rp2", true, "should we attempt to recognize binary primitives?");
		public final boolean recognizePrimitive3 = addB("recognizePrimitive3", "rp3", true, "should we attempt to recognize ternary primitives?");
		public final boolean recognizeReifLogic = addB("recognizeReifLogic", "rlog", true, "should we attempt to recognize logical reification forms?");
		public final boolean recognizeExtremum = addB("recognizeExtremum", "rext", true, "should we attempt to recognize minimum/maximum constraints?");
		public final boolean recognizeSum = addB("recognizeSum", "rsum", true, "should we attempt to recognize sum constraints?");

		public boolean toExtension(Variable[] vars) {
			return vars.length <= arityLimitToExtension && Constraint.howManyVariablesWithin(vars, spaceLimitToExtension) == Constants.ALL;
		}
	}

	public class SettingGlobal extends SettingGroup {
		public final int allDifferent = addI("allDifferent", "g_ad", 0, "Algorithm for AllDifferent");
		public final int distinctVectors = addI("distinctVectors", "g_dv", 0, "Algorithm for DistinctVectors");
		public final int allEqual = addI("allEqual", "g_ae", 0, "Algorithm for AllEqual");
		public final int notAllEqual = addI("notAllEqual", "g_nae", 0, "Algorithm for NotAllEqual");
		public final int noOverlap = addI("noOverlap", "g_no", 0, "Algorithm for NoOverlap");
		public final boolean redundNoOverlap = addB("redundNoOverlap", "r_no", true, "");
		public final int binpacking = addI("binpacking", "g_bp", 0, "Algorithm for BinPacking");
		public final boolean viewForSum = addB("viewForSum", "vs", false, "Should we use views for Sum constraints, when possible?");
		public final boolean permutations = addB("permutations", "", false, "Use permutation constraints for AllDifferent if possible (may be faster)");
		public final int allDifferentNb = addI("allDifferentNb", "iad", 0, "Number of possibly automatically inferred AllDifferent");
		public final int allDifferentSize = addI("allDifferentSize", "iadsz", 5, "Limit on the size of possibly automatically inferred AllDifferent");

		public final boolean starred = addB("starred", "", false, "When true, some global constraints are encoded by starred tables");
		public final boolean hybrid = addB("hybrid", "", false, "When true, some global constraints are encoded by hybrid/smart tables");
	}

	public class SettingPropagation extends SettingGroup {
		String s_uaq = "If enabled, queues of constraints are used in addition to the queue of variables. The purpose is to propagate less often the most costly constraints.";

		public String clazz = addS("clazz", "p", AC.class, null, "Class to be used for propagation (for example, FC, AC or SAC3)");
		public final int variant = addI("variant", "pv", 0, "Propagation Variant (only used for some consistencies)", HIDDEN);
		public final boolean useAuxiliaryQueues = addB("useAuxiliaryQueues", "uaq", false, s_uaq);
		public final String reviser = addS("reviser", "reviser", Reviser3.class, Reviser.class, "class to be used for performing revisions");
		public boolean residues = addB("residues", "res", true, "Must we use redidues (AC3rm)?");
		public boolean bitResidues = addB("bitResidues", "bres", true, "Must we use bit resides (AC3bit+rm)?");
		public final boolean multidirectionality = addB("multidirectionality", "mul", true, "");

		// three ways of control on (G)AC for intention constraints
		public final int futureLimit = addI("futureLimit", "fl", -1,
				"AC not enforced when the number of future variables is greater than this value (if not -1)");
		public final int spaceLimit = addI("spaceLimit", "sl", 20,
				"AC not enforced when size of the Cartesian product of domains is  greater than 2 to the power of this value (if not -1)");
		public final int arityLimit = addI("arityLimit", "al", 2, "AC not enforced if the arity is greater than this value");

		public boolean strongOnlyAtPreprocessing = addB("strongOnlyAtPreprocessing", "sop", false, "");
		public final boolean strongOnlyWhenACEffective = addB("strongOnlyWhenACEffective", "soe", false, "");
		public final boolean strongOnlyWhenNotSingleton = addB("strongOnlyWhenNotSingleton", "sons", true, "");
		public final int weakCutoff = addI("weakCutoff", "wc", 15, "");
	}

	public class SettingShaving extends SettingGroup {
		public int parameter = addI("parameter", "s_p", 1, "", HIDDEN);
		public final double eligibilityThreshod = addD("eligibilityThreshod", "s_et", 3.0, "", HIDDEN);
		public final int limitedPropagationSamplingSize = addI("limitedPropagationSamplingSize", "s_lpss", 100, "", HIDDEN);
		public final double ratio = addD("ratio", "s_r", 0.0, "");
		public final double alpha = addD("alpha", "s_a", 0.0, "");
	}

	public class SettingLNS extends SettingGroup {
		public final boolean enabled = addB("enabled", "lns_e", false, "LNS activated if true");
		public final String clazz = addS("clazz", "lns_h", Rand.class, null, "class to be used as freezing heuristic");
		public final int nFreeze = addI("nFreeze", "lns_n", 0, "number of variables to freeze when restarting.");
		public final int pFreeze = addI("pFreeze", "lns_p", 10, "percentage of variables to freeze when restarting.");
	}

	public class SettingSolving extends SettingGroup {
		public String clazz = addS("clazz", "s_class", Solver.class, null, "The name of the class used to explore the search space");
		public boolean enablePrepro = addB("enablePrepro", "prepro", true, "must we perform preprocessing?");
		public boolean enableSearch = addB("enableSearch", "search", true, "must we perform search?");
		public final Branching branching = addE("branching", "branching", Branching.BIN, "Branching scheme for search (binary or non-binary)");
	}

	public class SettingRestarts extends SettingGroup {
		String s_c = "The number of the counter (number of backtracks, number of failed assignments, ...) before the solver restarts."
				+ "\n\tWhen no value is given, the cutoff is set to Integer.MAX_VALUE.";
		String s_rrp = "Period, in term of number of restarts, for resetting restart data.";
		String s_rrc = "Coefficient used for increasing the cutoff, when restart data are reset";

		public int nRunsLimit = addI("nRunsLimit", "r_n", Integer.MAX_VALUE, "maximal number of runs (restarts) to be performed");
		public long cutoff = addL("cutoff", "r_c", 10, s_c); // for COP, it is initially multiplied by 10 in Restarter
		public double factor = addD("factor", "r_f", 1.1, "The geometric increasing factor when updating the curtoff");
		public final RestartMeasure measure = addE("measure", "r_m", RestartMeasure.FAILED, "The metrics used for measuring and comparing to the cutoff");
		public int nRestartsResetPeriod = addI("nRestartsResetPeriod", "r_rrp", 90, s_rrp);
		public final int nRestartsResetCoefficient = addI("nRestartsResetCoefficient", "r_rrc", 2, s_rrc);
		public final int varhResetPeriod = addI("varhResetPeriod", "r_rp", Integer.MAX_VALUE, "");
		public final int varhSolResetPeriod = addI("varhSolResetPeriod", "r_srp", 30, "");
		public boolean restartAfterSolution = addB("restartAfterSolution", "ras", false, "");
		public boolean luby = addB("luby", "r_luby", false, "True if a Luby series must be used instead of a geometric one");
	}

	public class SettingLearning extends SettingGroup {
		public LearningNogood nogood = addE("nogood", "l_ng", LearningNogood.RST, "Nogood recording technique (nogood recording from restarts by default)");
		public final int nogoodBaseLimit = addI("nogoodBaseLimit", "l_ngbl", 200000, "The maximum number of nogoods that can be stored in the base");
		public final int nogoodArityLimit = addI("nogoodArityLimit", "l_ngal", Integer.MAX_VALUE, "The maximum arity of a nogood that can be recorded", HIDDEN);
		public final LearningIps ips = addE("ips", "ips", LearningIps.NO, "IPS extraction technique (currently, no such learning by default)");
		public final String ipsOperators = addS("ipsOperators", "ipso", "11011", "Reduction operators for IPSs; a sequence of 5 bits is used").trim();
		public final int ipsCompressionEquivalence = addI("ipsCompressionEquivalence", "ipsc", Deflater.NO_COMPRESSION, "", HIDDEN);
		// BEST_SPEED or BEST_COMPRESSION as alternatives
		public final int ipsCompressionLimitEquivalence = addI("ipsCompressionLimitEquivalence", "ipscl", 300, "", HIDDEN);
	}

	public class SettingRevh extends SettingGroup {
		public final String clazz = addS("clazz", "revh", Dom.class, HeuristicRevisions.class, "class of the revision ordering heuristic");
		public final boolean anti = addB("anti", "anti_revh", false, "reverse of the natural heuristic order?");
	}

	public class SettingVarh extends SettingGroup {
		public final String clazz = addS("clazz", "varh", Wdeg.class, HeuristicVariables.class, "class of the variable ordering heuristic");
		public final boolean anti = addB("anti", "anti_varh", false, "reverse of the natural heuristic order?");
		public final int lc = addI("lc", "lc", 2, "value for lc (last conflict); 0 if not activated");
		public final ConstraintWeighting weighting = addE("weighting", "wt", ConstraintWeighting.CACD, "how to manage weights for wdeg variants");
		public final SingletonStrategy singleton = addE("singleton", "sing", SingletonStrategy.LAST, "how to manage singleton variables during search");
		public final boolean discardAux = addB("discardAux", "da", false, "must we not branch on auxiliary variables introduced by the solver?");
	}

	public class SettingValh extends SettingGroup {
		public final String clazz = addS("clazz", "valh", First.class, HeuristicValues.class, "class of the value ordering heuristic");
		public final boolean anti = addB("anti", "anti_valh", false, "reverse of the natural heuristic order?");
		public final boolean runProgressSaving = addB("runProgressSaving", "rps", false, "run progress saving");
		public final int solutionSaving = addI("solutionSaving", "sos", 1, "solution saving (0 disabled, 1 enabled, otherwise desactivation period");
		public final String warmStart = addS("warmStart", "warm", "", "a starting instantiation (solution) to be used with solution saving");

		public final boolean bivsFirst = addB("bivsFirst", "bivs_f", true, "bivs stopped at first found solution?");
		public final boolean bivsOptimistic = addB("bivsOptimistic", "bivs_o", true, "optimistic bivs mode? (or pessimistic?)");
		public final int bivsDistance = addI("bivsDistance", "bivs_d", 2, "0: only if in the objective constraint; 1: if at distance 0 or 1; 2: any variable");
		public final int bivsLimit = addI("bivsLimit", "bivs_l", Integer.MAX_VALUE, "bivs applied only if the domain size is <= bivsl");
		public final boolean optValHeuristic = addB("optValHeuristic", "ovh", false, "");
	}

	public class SettingExtraction extends SettingGroup {
		String s = "\n\tValid only with the command: java " + HeadExtraction.class.getName();

		public final Extraction method = addE("method", "e_m", Extraction.VAR, "method for extracting unsatisfiable cores." + s);
		public final int nCores = addI("nCores", "e_nc", 1, "number of unsatifiable cores to be extracted." + s);
	}

	public class SettingExperimental extends SettingGroup {
		public int testI1 = addI("testI1", "testI1", 0, "", HIDDEN);
		public int testI2 = addI("testI2", "testI2", 0, "", HIDDEN);
		public int testI3 = addI("testI3", "testI3", 0, "", HIDDEN);
	}

	/**********************************************************************************************
	 ***** Handling user settings (from the command line, and also possibly from a file)
	 *********************************************************************************************/

	/**
	 * This class allows us to deal with options given by the user, either on the command line or by means of an XML
	 * control file
	 */
	public class UserSettings {

		public static final String ALL = "all";
		public static final String MIN = "min";
		public static final String MAX = "max";

		/**
		 * The document for the XML control file specified by the user (may be null)
		 */
		private Document document;

		/**
		 * The object useful to make requests on the document
		 */
		private XPath xPath;

		public final String controlFilename;

		private UserSettings(String controlFilename) {
			this.controlFilename = controlFilename != null ? controlFilename : Input.controlFilename;
			if (controlFilename != null && !controlFilename.equals(Input.DEFAULT_SETTINGS)) {
				// Loads the XML file containing all settings from the user.
				this.document = Kit.load(new File(controlFilename));
				this.xPath = XPathFactory.newInstance().newXPath();
			}
		}

		/** Returns the value (a String) of the specified attribute for the specified tag. */
		private String stringFor(String shortcut, String tag, String att, Object defaultValue) {
			// try with shortcut
			String s = shortcut == null ? null : Input.argsForSolving.get(shortcut);
			if (s != null)
				return s.length() == 0 && !(defaultValue instanceof String) ? defaultValue.toString() : s;
			// try with tag+attribute
			s = Input.argsForSolving.get((tag != null ? tag + "/" : "") + att);
			if (s != null)
				return s;
			if (document == null)
				return defaultValue.toString();
			try { // try in document
				NodeList nodes = (NodeList) xPath.compile("//" + (tag != null ? tag : "*") + "/@" + att).evaluate(document, XPathConstants.NODESET);
				control(nodes.getLength() <= 1, () -> "Problem with several possibilities for " + tag + " " + att);
				if (nodes.getLength() == 0)
					return defaultValue.toString();
				s = nodes.item(0).getNodeValue();
				return s.length() == 0 && !(defaultValue instanceof String) ? defaultValue.toString() : s;
			} catch (XPathExpressionException e) {
				Kit.exit("problem xpath", e);
			}
			return (String) Kit.exit("Problem with " + tag + " and " + att + " and " + defaultValue);
		}

		private Number numberFor(String shortcut, String tag, String att, Object defaultValue, boolean longValue) {
			String s = stringFor(shortcut, tag, att, defaultValue).toLowerCase();
			if (s.equals(MIN))
				return longValue ? Long.MIN_VALUE : (Number) Integer.MIN_VALUE; // problem if cast omitted
			if (s.equals(MAX) || s.equals(ALL))
				return longValue ? Long.MAX_VALUE : (Number) Integer.MAX_VALUE; // problem if cast omitted
			char lastCharacter = s.charAt(s.length() - 1);
			Long baseValue = Kit.parseLong(Character.isDigit(lastCharacter) ? s : s.substring(0, s.length() - 1));
			control(baseValue != null, () -> "An integer/long value was expected for " + tag + "/" + att);
			double value = Character.isDigit(lastCharacter) ? baseValue
					: lastCharacter == 'k' || lastCharacter == 's' ? baseValue * 1000
							: lastCharacter == 'm' ? baseValue * 1000000 : (Double) Kit.exit("Bad character for " + tag + " " + att);
			control((longValue && Long.MIN_VALUE <= value && value <= Long.MAX_VALUE)
					|| (!longValue && Integer.MIN_VALUE <= value && value <= Integer.MAX_VALUE));
			return longValue ? (long) value : (Number) (int) value; // BE CAREFUL: problem if cast omitted
		}

		/** Returns the value (an integer) of the specified attribute for the specified tag. */
		private int intFor(String shortcut, String tag, String att, Integer defaultValue) {
			return (Integer) numberFor(shortcut, tag, att, defaultValue, false);
		}

		/** Returns the value (a long integer) of the specified attribute for the specified tag. */
		private Long longFor(String shortcut, String tag, String att, Long defaultValue) {
			return (Long) numberFor(shortcut, tag, att, defaultValue, true);
		}

		/** Returns the value (a double) of the specified attribute for the specified tag. */
		private double doubleFor(String shortcut, String tag, String att, Double defaultValue) {
			Double d = Utilities.toDouble(stringFor(shortcut, tag, att, defaultValue));
			control(d != null, () -> "A double value was expected for " + tag + "/" + att);
			return d;
		}

		/** Returns the value (a boolean) of the specified attribute for the specified tag. */
		private boolean booleanFor(String shortcut, String tag, String att, Boolean defaultValue) {
			Boolean b = Utilities.toBoolean(stringFor(shortcut, tag, att, defaultValue));
			control(b != null, () -> "A boolean value was expected for " + tag + "/" + att);
			return b;
		}
	}

}
