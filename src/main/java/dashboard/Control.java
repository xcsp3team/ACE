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
import java.util.List;
import java.util.Scanner;
import java.util.logging.Level;
import java.util.stream.IntStream;
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
import org.xcsp.common.IVar;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeCtr;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeParent;

import constraints.Constraint;
import constraints.ConstraintExtension.Extension;
import constraints.extension.structures.Bits;
import constraints.extension.structures.Matrix.Matrix3D;
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
import main.HeadExtraction.Extraction;
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
 * This class allows us to manage all options concerning the problem (typically, the way to represent it) and the solver (typically, the way to conduct search).
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
			System.out.println("\tTool used to generate a default option control file.");
			System.out.println("\tUsage : " + Control.class.getName() + " <outputFileName> <maximumPriority>");
			System.out.println("\n\toutputFileName : name of the generated option control file.");
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

	public final OptionsGeneral general;

	public final OptionsProblem problem;
	public final OptionsVariables variables;
	public final OptionsConstraints constraints;
	public final OptionsOptimization optimization;

	public final OptionsExtension extension;
	public final OptionsIntension intension;
	public final OptionsGlobal global;

	public final OptionsPropagation propagation;
	public final OptionsShaving shaving;
	public final OptionsLearning learning;

	public final OptionsSolving solving;
	public final OptionsRestarts restarts;
	public final OptionsLNS lns;

	public final OptionsRevh revh;
	public final OptionsVarh varh;
	public final OptionsValh valh;

	public final OptionsExtraction extraction;

	public Control(String controlFilename) {
		this.options = new ArrayList<>();
		this.userSettings = new UserSettings(controlFilename);

		this.general = new OptionsGeneral();

		this.problem = new OptionsProblem();
		this.variables = new OptionsVariables();
		this.constraints = new OptionsConstraints();
		this.optimization = new OptionsOptimization();

		this.extension = new OptionsExtension();
		this.intension = new OptionsIntension();
		this.global = new OptionsGlobal();

		this.propagation = new OptionsPropagation();
		this.shaving = new OptionsShaving();
		this.learning = new OptionsLearning();

		this.solving = new OptionsSolving();
		this.restarts = new OptionsRestarts();
		this.lns = new OptionsLNS();

		this.revh = new OptionsRevh();
		this.varh = new OptionsVarh();
		this.valh = new OptionsValh();

		this.extraction = new OptionsExtraction();

		general.verbose = general.verbose < 1 && general.trace.length() > 0 ? 1 : general.verbose;
		control(-1 <= general.verbose && general.verbose <= 3, () -> "Verbose must be in -1..3");
		Kit.log.setLevel(general.verbose == -1 ? Level.OFF
				: general.verbose == 0 ? Level.CONFIG : general.verbose == 1 ? Level.FINE : general.verbose == 2 ? Level.FINER : Level.FINEST);
		control(0 <= lns.pFreeze && lns.pFreeze < 100, () -> "percentageOfVariablesToFreeze should be between 0 and 100 (excluded)");
		control(learning.nogood == LearningNogood.NO || learning.nogood == LearningNogood.RST, "other values currently not available");
		control(optimization.lb <= optimization.ub);
		controlKeys();
		if (general.exceptionsVisible)
			org.xcsp.modeler.Compiler.ev = true;
		if (general.noPrintColors)
			Kit.useColors = false;
		// if (framework == TypeFramework.MAXCSP) optimization.lb = 0L;
		if (general.runRobin) {
			varh.clazz = "RunRobin";
			valh.clazz = "RunRobin";
			if (valh.solutionSavingStart == -1)
				valh.solutionSavingStart = 12;
			restarts.cutoff = restarts.cutoff / 2;
			restarts.factor = 1.05;
		}
	}

	public void framework(Optimizer optimizer) {
		if (optimizer != null) {
			if (general.solLimit == -1)
				general.solLimit = PLUS_INFINITY; // default value for COP (in order to find an optimum)
			// if (optimizer.ctr instanceof MaximumCstLE || optimizer.ctr instanceof MinimumCstGE) // || optimizer.ctr
			// // instanceof ObjectiveVariable) restarts.restartAfterSolution = true;
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
			s += "\tDefault value is: " + (defaultValue instanceof String && ((String) defaultValue).length() == 0 ? "\"\" (empty string)" : defaultValue)
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

	private class OptionGroup {

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
			control(getClass().getSimpleName().startsWith("Options"));
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

	public class OptionsGeneral extends OptionGroup {
		String s_verbose = "\n\t0 : only some global statistics are listed;" + "\n\t1 : in addition, solutions are  shown;"
				+ "\n\t2 : in addition, additionnal information about the problem instance to be solved is given;"
				+ "\n\t3 : in addition, for each constraint, allowed or unallowed tuples are displayed.";

		// below, -1 when not initialized
		public long solLimit = addL("solLimit", "s", -1, "The limit on the number of found solutions before stopping; for no limit, use -s=all or s=-1");
		public final long timeout = addL("timeout", "t", PLUS_INFINITY, "The limit in milliseconds before stopping; seconds can be indicated as in -t=10s");
		public final String discardClasses = addS("discardClasses", "dc", "", "XCSP3 classes (tags) to be discarded (comma as separator)");
		public final String campaignDir = addS("campaignDir", "cd", "", "Name of a campaign directory where results (XML files) are stored.");
		public final String trace = addS("trace", "trace", "", "Displays a trace (with possible depth control as eg -trace=10-20");
		public final boolean removedAfterProcessing = addB("removedAfterProcessing", "rap", false, "Displaying removed values after preprocessing ?");

		public final int jsonLimit = addI("jsonLimit", "jl", 10000, "The limit on the number of variables for displaying solutions in JSON");
		public final boolean jsonAux = addB("jsonAux", "ja", false, "Take auxiliary variables when displaying solutions in JSON");
		public final String jsonSave = addS("jsonSave", "js", "", "Save the first solution in a file whose name is this value");
		public final boolean jsonQuotes = addB("jsonQuotes", "jq", false, "Surround keys with quotes when solutions are displayed on the standard output");
		public final boolean jsonEachSolution = addB("jsonEachSolution", "je", false, "During search, display all found solutions in JSON");

		public final boolean solutionHamming = addB("solutionHamming", "sh", true,
				"During search, display the Hamming distance between two successive solutions");
		
		public final boolean xmlCompact = addB("xmlCompact", "xc", true, "Compress values when displaying solutions in XML");
		public final boolean xmlEachSolution = addB("xmlEachSolution", "xe", false, "During search, display all found solutions in XML");
		public final boolean saveSolutions = addB("storeSolutions", "sts", false, "Save all found solutions in a JSON file?");
		public final boolean noPrintColors = addB("noPrintColors", "npc", false, "Don't use special color characters in the terminal");
		public final boolean exceptionsVisible = addB("exceptionsVisible", "ev", false, "Makes exceptions visible.");
		public final boolean enableAnnotations = addB("enableAnnotations", "ea", false, "Enables annotations (currently, mainly concerns priority variables).");
		public final int satisfactionLimit = addI("satisfactionLimit", "satl", PLUS_INFINITY_INT, "Converting the objective into a constraint with this limit");
		public final long seed = addL("seed", "seed", 0, "The seed that can be used for some random-based methods.");
		public int verbose = addI("verbose", "v", 0, "Verbosity level (value between -1 and 3)" + s_verbose);
		public final boolean runRobin = addB("runRobin", "rr", false, "Using a Run Robin search strategy");
		public final boolean profiling = addB("profiling", "prof", false, "Using some very basic profiling information?");
		public final boolean controlSolutions = addB("controlSolutions", "cs", false, "Control solutions");
	}

	public class OptionsProblem extends OptionGroup {
		public final String data = addS("data", "", "", "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName());
		public final String variant = addS("variant", "", "", "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName());
		public final boolean shareBits = addB("shareBits", "", false, "Trying to save space by sharing bit vectors.");
		public final SymmetryBreaking symmetryBreaking = addE("symmetryBreaking", "sb", NO, "Symmetry-breaking method (requires Saucy to be installed)");
	}

	public class OptionsVariables extends OptionGroup {
		String s_sel = "Allows us to give a list of variable that will form the subproblem to be solved."
				+ "\n\tThis list is composed of a sequence of tokens separated by commas (no whitespace)."
				+ "\n\tEach token is a variable id a variable number or an interval of the form i..j with i and j integers."
				+ "\n\tFor example, -sel=2..10,31,-4 will denote the list 2 3 5 6 7 8 9 10 31." + "\n\tThis is only valid for a XCSP instance.";
		String s_insref = "Allows us to give an instantiation (-ins) or refutation (-ref) of variables for the problem to be solved."
				+ "\n\tThis instantiation/refutation is given under the form vars:values."
				+ "\n\tvars is a sequence of variable ids or numbers separated by commas (no whitespace)."
				+ "\n\tvalues is a sequence of integers (the values for variables) separated by commas (no whitespace)."
				+ "\n\tFor example, -ins=x2,x4,x9:1,11,4 will denote the instantiation {x2=1,x4=11,x9=4} (or refutation).";
		String s_pr1 = "Allows us to give a list of variables that will become strict priority variables (to be used by the variable ordering heuristic)."
				+ "\n\tThis list is composed of a sequence of strings (ids of variables) or integers (numbers of variables) separated by commas (no whitespace)."
				+ "\n\tFor example, -pr1=2,8,1,10 will denote the list 2 8 1 10.";
		String s_pr2 = "Allows us to give a list of variables that will become (non strict) priority variables."
				+ "\n\tThis list is composed of a sequence of tokens separated by commas (no whitespace)."
				+ "\n\tEach token is variable id, a variable number (integer) or an interval of the form i..j with i and j integers.."
				+ "\n\tFor example, -pr2=2..10,31,-4 will denote the list 2 3 5 6 7 8 9 10 31.";

		public final String selection = addS("selection", "sel", "", s_sel);
		public final String instantiation = addS("instantiation", "ins", "", s_insref);
		public final String refutation = addS("refutation", "ref", "", s_insref);
		public final String priority1 = addS("priority1", "pr1", "", s_pr1);
		public final String priority2 = addS("priority2", "pr2", "", s_pr2);
		public final String priorityArrays = addS("priorityArrays", "pra", "", "Index(es) or id(s) of the variable array(s) that must be assigned in priority");
		public final String projectionArrays = addS("projectionArrays", "pja", "", "Index(es) or id(s) of the variable array(s) that must be projected");
		public final boolean stayArrayFocus = addB("stayArrayFocus", "saf", false, "Should we stay focused on arrays when assigning variables");
		public final boolean omit0DegreeVariables = addB("omit0DegreeVariables", "omv", true, "Ommit variables of degree 0");
		public final boolean reduceIsolated = addB("reduceIsolated", "riv", true, "Arbitrary keeping a single value in the domain of isolated variables");
		public final boolean useSpecialVariables = addB("useSpecialVariables", "usv", false, "Use special variables for large domains?");
		public final int specialDomainLimit = addI("specialDomainLimit", "sdl", 2_000, "Domain size limit for building special variables");
	}

	public class OptionsConstraints extends OptionGroup {
		public final boolean preserve1 = addB("preserve1", "pc1", true, "Must we keep unary constraints (instead of filtering them straight)");
		public final TypeCtr ignoredType = Types.valueOf(TypeCtr.class, addS("ignoreType", "", "", "Dicard all constraints of this type"));
		public final int ignoreArity = addI("ignoreArity", "", -1, "Discard all constraints of this arity");
		public final String ignoreGroups = addS("ignoreGroups", "ig", "", "Index(es) of the group(s) of constraints that must be discarded");
		public final int positionsLb = addI("positionsLb", "poslb", 3, "Minimal arity to build the array positions");
		public final int positionsUb = addI("positionsUb", "posub", 10000, "Maximal number of variables to build the array positions");
		public final int nogoodsMergingLimit = addI("nogoodsMergingLimit", "nml", 3, "Limit for merging (in a table) nogoods of same scope");
		public final boolean postCtrTrues = addB("postCtrTrues", "pct", false, "Must we post CtrTrue encountered while loading/reformualting constraints?");

		public final boolean discardHybridEntailment = addB("discardHybridEntailment", "dec", true,
				"Must we discard the mechansim of hybrid table entailment?");
	}

	public class OptionsOptimization extends OptionGroup {
		public long lb = addL("lb", "", MINUS_INFINITY, "Initial lower bound");
		public long ub = addL("ub", "", PLUS_INFINITY, "Initial upper bound");
		public final OptimizationStrategy strategy = addE("strategy", "os", OptimizationStrategy.DECREASING, "Optimization strategy");
		public final boolean replaceObjVar = addB("replaceObjVar", "rov", true,
				"Must we replace the objective variable by an objective constraint, when possible?");
		public final boolean keepTree = addB("keepTree", "kt", false,
				"Must we keep the objective as it is when given under the form of a tree (except if a sum is recognized)?");
		public final boolean replaceMinMaximum = addB("replaceMinMaximum", "rmm", true,
				"Must we use a single aux variable when minimizing the maximum of trees ?");
		public final int boundDescentCoeff = addI("boundDescentCoeff", "bdc", 1, "Bound descent coefficient");

		// public final boolean discardObjective = addB("discardObjective", "do", false, "Discard the objective if any");
	}

	public class OptionsExtension extends OptionGroup {
		public final Extension positive = addE("positive", "", Extension.CT, "Algorithm for (non-binary) positive table constraints");
		public final Extension negative = addE("negative", "", Extension.V, "Algorithm for (non-binary) negative table constraint");
		public final boolean generic2 = addB("generic2", "", true, "Must we use a generic filtering scheme for binary table constraints?");
		public final String structureClass2 = addS("structureClass2", "sc2", Bits.class, null, "Structures to be used for binary table constraints");
		public final String structureClass3 = addS("structureClass3", "sc3", Matrix3D.class, null, "Structures to be used for ternary table constraints");
		public final int arityLimitToPositive = addI("arityLimitToPositive", "alp", -1, "Limit on arity for converting negative table constraints to positive");
		public final int arityLimitToNegative = addI("arityLimitToNegative", "aln", -1, "Limit on arity for converting positive table constraints to negative");
		public final int variant = addI("variant", "extv", 0, "Variant to be used for some algorithms (e.g., VA or CMDD)");
		public final boolean decremental = addB("decremental", "extd", true, "Must we use a decremental mode for some algorithms (e.g., STR2, CT or CMDD)");
		public final int smallTableExt = addI("smallTableExt", "stext", 16, "table size threshold for considering a special propagator");
		public final int largeScopeExt = addI("largeScopeExt", "lsext", 50, "scope size threshold for considering a special propagator");
		public final boolean toMDD = addB("toMDD", "tomdd", false, "Must we attempt to convert extension constraints into MDDs (if possible)");

		public boolean reverse(int arity, boolean positive) {
			return (positive && arity <= arityLimitToNegative) || (!positive && arity <= arityLimitToPositive);
		}
	}

	public class OptionsIntension extends OptionGroup {
		public final int decompose = addI("decompose", "di", 1, "0: no decomposition, 1: conditional decomposition, 2: forced decompostion");
		public final boolean toExtension1 = addB("toExtension1", "ie1", true, "Must we convert unary intension constraints to extension?");
		public final int arityLimitToExtension = addI("arityLimitToExtension", "ale", 0, "Limit on arity for possibly converting to extension");
		public final int spaceLimitToExtension = addI("spaceLimitToExtension", "sle", 20, "Limit on space for possibly converting to extension");
		public final int spaceLimitToNogood = addI("spaceLimitToNogood", "sln", 0, "Limit on space for possibly converting to nogoods");
		// The following options determine whether special forms of intension constraints must be recognized/intercepted
		public final boolean recognizePrimitive2 = addB("recognizePrimitive2", "rp2", true, "Must we attempt to recognize binary primitives?");
		public final boolean recognizePrimitive3 = addB("recognizePrimitive3", "rp3", true, "Must we attempt to recognize ternary primitives?");
		public final boolean recognizeReifLogic = addB("recognizeReifLogic", "rlog", true, "Must we attempt to recognize logical reification forms?");
		public final boolean recognizeExtremum = addB("recognizeExtremum", "rext", true, "Must we attempt to recognize minimum/maximum constraints?");
		public final boolean recognizeSum = addB("recognizeSum", "rsum", true, "Must we attempt to recognize sum constraints?");
		public final boolean recognizeIf = addB("recognizeIf", "rif", true, "Must we recognize/decompose the ternary operator if?");
		public final int recognizeXor = addI("recognizeXor", "rxo", 1, "Must we recognize Xor constraints (two modes 1 and 2)?");
		public final boolean recognizeEqAnd = addB("recognizeEqAnd", "rea", false, "Must we recognize an expression eq-and (or iff-and)?");
		public final int arityForClauseUnaryTrees = addI("arityForClauseUnaryTrees", "acut", PLUS_INFINITY_INT,
				"Arity for recognizing clauses on unary tree expressions");
		public final int arityForClauseHybridTrees = addI("arityForClauseHybridTrees", "acht", PLUS_INFINITY_INT,
				"Arity for recognizing clauses on hybrid tree expressions");
		public final boolean toHybrid = addB("toHybrid", "toh", false, "Must we convert toward hybrid tables, when possible?");
		public final boolean replaceSimilarInternNodes = addB("replaceSimilarInternNodes", "rsin", true, "Replace similar intern nodes by same variables?");
		public final int replaceSimilarInternNodesExcludingLimit = addI("replaceSimilarInternNodesExcludingLimit", "rsinel", 1,
				"Limit for replacing similar intern nodes"); // should we set it to 2?
		public final boolean displayRemainingIntension = addB("displayRemainingIntension", "dri", false,
				"Must we display the predicates of remaining intensional constraints");

		public boolean toExtension(Variable[] vars, XNode<IVar> tree) {
			Variable[] t = tree == null || !(tree instanceof XNodeParent) || !((XNodeParent<?>) tree).isEqVar() ? vars
					: IntStream.range(0, vars.length - 1).mapToObj(i -> vars[i]).toArray(Variable[]::new);
			return t.length <= arityLimitToExtension && Constraint.howManyVariablesWithin(t, spaceLimitToExtension) == Constants.ALL;
		}
	}

	public class OptionsGlobal extends OptionGroup {
		public final int allDifferent = addI("allDifferent", "g_ad", 0, "Algorithm for AllDifferent");
		public final int allDifferentExcept = addI("allDifferentExcept", "g_ade", 0, "Algorithm for AllDifferentExcept");
		public final boolean gatherAllDifferent = addB("gatherAllDifferent", "g_gad", false, "");
		public final int distinctVectors = addI("distinctVectors", "g_dv", 0, "Algorithm for DistinctVectors");
		public final int allEqual = addI("allEqual", "g_ae", 0, "Algorithm for AllEqual");
		public final boolean redundantSumForCounts = addB("redundantSumForCounts", "rcs", true,
				"Must we try to post redudant sums for several counts acting as cardinality?");
		public final int element = addI("element", "g_elt", 0, "Algorithm for Element");
		public final int circuit = addI("circuit", "g_circ", 1, "Algorithm for Circuit");
		public final int cumulativeAux = addI("cumulativeAux", "g_cua", 0, "Limit for introducing aux variables for Cumulative");
		public final int noOverlap1 = addI("noOverlap1", "g_no1", 0, "Algorithm for NoOverlap 1D");
		public final int noOverlap2 = addI("noOverlap2", "g_no2", 0, "Algorithm for NoOverlap 2D");
		public final int noOverlap3 = addI("noOverlap3", "g_no3", 12, "Algorithm for NoOverlap 3D");
		public final boolean noOverlapAux = addB("noOverlapAux", "g_noa", true, "Introducing aux variables for NoOverlap (when relevant)?");
		public final int noOverlapRedundLimit = addI("noOverlapRedundLimit", "g_nor", 10, "Arity limit for posting redundant constraints for NoOverlap?");
		public final int binpacking = addI("binpacking", "g_bp", 0, "Algorithm for BinPacking");
		public final boolean binpackingRedun = addB("binpackingRedun", "g_bpr", false, "Redundant constraints for for BinPacking");
		public final boolean viewForSum = addB("viewForSum", "vs", false, "Must we use views for Sum constraints, when possible?");
		public final boolean eqDecForSum = addB("eqDecForSum", "eqs", false,
				"Must we post two constraints for Sum constraints, when the operator is EQ (or IN)?");
		public final boolean eqMddForSum = addB("eqMddForSum", "eqm", false,
				"Must we post a MDD constraint for Sum constraints, when the operator is EQ (or IN)?");
		public final int sumeqToTableSpaceLimit = addI("sumeqToTableSpaceLimit", "set", 8, "Limit on space for possibly converting sumeq to table");
		public final int suminToTableSpaceLimit = addI("suminToTableSpaceLimit", "sit", 12, "Limit on space for possibly converting sumin to table");
		public final boolean permutation = addB("permutation", "", false, "Must we use permutation constraints for AllDifferent if possible? (may be faster)");
		public final int allDifferentNb = addI("allDifferentNb", "adn", 10, "Number of possibly automatically inferred AllDifferent");
		public final int allDifferentSize = addI("allDifferentSize", "ads", 5, "Limit on the size of possibly automatically inferred AllDifferent");

		public final boolean test = addB("test", "test", false, "");
		public final boolean test2 = addB("test2", "test2", false, "");
		// public final boolean starred = addB("starred", "", false, "When true, some global constraints are encoded by starred tables");
		// public final boolean hybrid = addB("hybrid", "", false, "When true, some global constraints are encoded by hybrid/smart tables");
	}

	public class OptionsPropagation extends OptionGroup {
		public final String clazz = addS("clazz", "p", AC.class, null, "Class to be used for propagation (for example, FC, AC or SAC3)");
		public final int variant = addI("variant", "pv", 0, "Propagation Variant (only used for some consistencies)");
		public final int postponableLimit = addI("postponableLimit", "ppc", 100, "Arity limit for postponing the filtering of expensive constraints");
		// above, the purpose is to propagate less often the most costly constraints (to be finalized)
		public final String reviser = addS("reviser", "", Reviser3.class, Reviser.class, "Class to be used for performing revisions");
		public final boolean residues = addB("residues", "res", true, "Must we use redidues (AC3rm)?");
		public final boolean bitResidues = addB("bitResidues", "bres", true, "Must we use bit resides (AC3bit+rm)?");
		public final boolean multidirectionality = addB("multidirectionality", "mul", true, "Must we use multidirectionality");
		// now, two ways of control on (G)AC for intention constraints
		public final int arityLimit = addI("arityLimit", "al", 1,
				"generic AC is systematically enforced if the arity is less than or equal to this value (or this value is -1)");
		public final int spaceLimit = addI("spaceLimit", "sl", 20,
				"generic AC is systematically enforced if the size of the Cartesian product of domains is less than or equal to 2 to the power of this value (or this value is -1)");
		public boolean strongOnce = addB("strongOnce", "so", false, "Must we only apply the strong consistency (if chosen) before search?");
		public final boolean strongAC = addB("strongAC", "sac", false, "Must we only apply the strong consistency (if chosen) when AC is effective?");
		public final boolean justRefuted = addB("justRefuted", "jr", false, "Must we try to improve performances by exploiting just refuted variables?");
	}

	public class OptionsShaving extends OptionGroup {
		public final int parameter = addI("parameter", "s_p", 1, "", HIDDEN);
		public final double eligibilityThreshod = addD("eligibilityThreshod", "s_et", 3.0, "", HIDDEN);
		public final int limitedPropagationSamplingSize = addI("limitedPropagationSamplingSize", "s_lpss", 100, "", HIDDEN);
		public final double ratio = addD("ratio", "s_r", 0.0, "");
		public final double alpha = addD("alpha", "s_a", 0.0, "");
	}

	public class OptionsLearning extends OptionGroup {
		public final LearningNogood nogood = addE("nogood", "ng", LearningNogood.RST, "Nogood recording technique (from restarts by default)");
		public final int nogoodBaseLimit = addI("nogoodBaseLimit", "ngbl", 1_000_000, "The maximum number of nogoods that can be stored in the base");
		public final int nogoodArityLimit = addI("nogoodArityLimit", "ngal", Integer.MAX_VALUE, "The maximum arity of a nogood that can be recorded");
		public final LearningIps ips = addE("ips", "", LearningIps.NO, "IPS extraction technique (currently, no such learning by default)");
		public final String ipsOperators = addS("ipsOperators", "ipso", "11011", "Reduction operators for IPSs; a sequence of 5 bits is used");
		public final int ipsCompression = addI("ipsCompression", "ipsc", Deflater.NO_COMPRESSION, "IPS Compression for equivalence reasoning");
		// BEST_SPEED or BEST_COMPRESSION as alternatives
		public final int ipsCompressionLimit = addI("ipsCompressionLimit", "ipscl", 300, "IPS Compression limit for equivalence reasoning");
		public final int nogoodDisplayLimit = addI("nogoodDisplayLimit", "ndl", 0, "Size limit of the nogoods (from restarts) for being displayed");
	}

	public class OptionsSolving extends OptionGroup {
		public final String clazz = addS("clazz", "s_class", Solver.class, null, "Class for solving (usually, Solver)");
		public final boolean enablePrepro = addB("enablePrepro", "prepro", true, "Must we perform preprocessing?");
		public boolean enableSearch = addB("enableSearch", "search", true, "Must we perform search?");
		public final Branching branching = addE("branching", "branching", Branching.BIN, "Branching scheme for search (binary or non-binary)");
	}

	public class OptionsRestarts extends OptionGroup {
		public int nRuns = addI("nRuns", "r_n", Integer.MAX_VALUE, "Maximal number of runs (restarts) to be performed");
		public long cutoff = addL("cutoff", "r_c", 10, "Cutoff as a value of, e.g., the number of failed asignments before restarting");
		// the cutoff,for COP, it is initially multiplied by 10 in Restarter
		public double factor = addD("factor", "r_f", 1.1, "The geometric increasing factor when updating the cutoff");
		public final RestartMeasure measure = addE("measure", "r_m", RestartMeasure.FAILED, "The metrics used for measuring and comparing with the cutoff");
		public final int resetPeriod = addI("resetPeriod", "r_rp", 90, "Period, in term of number of restarts, for resetting restart data.");
		public final int resetCoefficient = addI("resetCoefficient", "r_rc", 2, "Coefficient used for increasing the cutoff, when restart data are reset");
		// public final int resetCoefficientMeta = addI("resetCoefficientMeta", "r_rcm", 270, "");
		public final int varhResetPeriod = addI("varhResetPeriod", "r_vrp", Integer.MAX_VALUE, "");
		public final int varhSolResetPeriod = addI("varhSolResetPeriod", "r_vsrp", 30, "");
		public boolean restartAfterSolution = addB("restartAfterSolution", "ras", false, "Must we restart every time a solution is found?");
		public final boolean luby = addB("luby", "", false, "Must we use a Luby series instead of a geometric one?");
		public final int solRunLimit = addI("solRunLimit", "srl", 10, "Limit on the number of solutions at each run");
	}

	public class OptionsLNS extends OptionGroup {
		public final boolean enabled = addB("enabled", "lns_e", false, "Must we activate LNS?");
		public final String clazz = addS("clazz", "lns_h", Rand.class, null, "Class of the freezing heuristic");
		public final int nFreeze = addI("nFreeze", "lns_n", 0, "Number of variables to freeze when restarting");
		public final int pFreeze = addI("pFreeze", "lns_p", 10, "Percentage of variables to freeze when restarting");
	}

	public class OptionsRevh extends OptionGroup {
		public final String clazz = addS("clazz", "revh", Dom.class, HeuristicRevisions.class, "Class of the revision ordering heuristic");
		public final boolean anti = addB("anti", "anti_revh", false, "Must we use the reverse of the natural heuristic order?");
		public final int revisionQueueLimit = addI("revisionQueueLimit", "rsl", 100, "Limit for searching the best variable in the revision queue");
	}

	public class OptionsVarh extends OptionGroup {
		public String clazz = addS("clazz", "varh", Wdeg.class, HeuristicVariables.class, "Class of the variable ordering heuristic");
		public final boolean anti = addB("anti", "anti_varh", false, "Must we use the reverse of the natural heuristic order?");
		public final int lc = addI("lc", "lc", 2, "Value for lc (last conflict); 0 if not activated");
		public final boolean lc1 = addB("lc1", "lc1", true, "Follow lc even if singleton domain?");
		public ConstraintWeighting weighting = addE("weighting", "wt", ConstraintWeighting.CACD, "How to manage weights for wdeg variants");
		public final int pickMode = addI("pickMode", "pm", 0, "How to manage incrementation of effective picked variables or constraints during propagation");
		public final boolean mvarh = addB("mvarh", "mvarh", false, "Must we just maintain an approximation of the best scored variable?");
		public final SingletonStrategy singleton = addE("singleton", "sing", SingletonStrategy.LAST, "How to manage singleton variables during search");
		public final boolean connected = addB("connected", "", false, "Must we select a variable necessarily connected to an already explicitly assigned one?");
		public final boolean discardAux = addB("discardAux", "da", false, "Must we not branch on auxiliary variables introduced by the solver?");
		public final boolean arrayPriorityRunRobin = addB("arrayPriorityRunRobin", "aprr", false, "Must we set priority to variable arrays in turn?");
		public final int mode = addI("mode", "mode", 0, "general option used differently according to the context");
		public final int lostDepth = addI("lostDepth", "ld", 0, "xx");
		public final int lostSize = addI("lostSize", "ls", 4, "xx");
		public final int optVarHeuristic = addI("optVarHeuristic", "ovarh", 0,
				"On how many variables must we branch in a fixed static way on the variables of the objective (when a weighted sum) according to coeff values?"); // experimental
		public final boolean alwaysAssignAllVariables = addB("alwaysAssignAllVariables", "aaa", false, "Must we always explicitly assign all variables?");
		public final boolean secondScored = addB("secondScored", "ssc", false, "Must we use the second variable scored by the heuristic?");
		public final boolean quitWhenBetterThanPreviousChoice = addB("quitWhenBetterThanPreviousChoice", "qwb", false,
				"Must we return a variable when its score is better than the score of the previously selected variable?");
		public final boolean frozen = addB("frozen", "frozen", false, "Must we freeze variables during runs?");
		public final int updateStackLength = addI("updateStackLength", "usl", 0, "Length of the stack used for recording sequentially better scored variables");
	}

	public class OptionsValh extends OptionGroup {
		public String clazz = addS("clazz", "valh", First.class, HeuristicValues.class, "Class of the value ordering heuristic");
		public final boolean anti = addB("anti", "anti_valh", false, "Must we use the reverse of the natural heuristic order?");
		public final boolean runProgressSaving = addB("runProgressSaving", "rps", false, "Must we use run progress saving?");
		public final boolean antiRunProgressSaving = addB("antiRunProgressSaving", "arps", false, "Must we use run anti progress saving?");

		public final int solutionSaving = addI("solutionSaving", "sos", 1, "Solution saving (0: disabled, 1: enabled, otherwise desactivation period");
		public final boolean solutionSavingExceptObj = addB("solutionSavingExceptObj", "sos_eo", false,
				"Must we discard variables of the objective function for sos?");
		public int solutionSavingStart = addI("solutionSavingStart", "sos_st", -1, "At which run solution saving must be activated?");
		public final String warmStart = addS("warmStart", "warm", "", "A starting instantiation (solution) to be used with solution saving");

		public final boolean bivsFirst = addB("bivsFirst", "bivs_f", true, "Must we stop BIVS at first found solution?");
		public final boolean bivsOptimistic = addB("bivsOptimistic", "bivs_o", true, "Must we use the optimistic BIVS mode?");
		public final int bivsDistance = addI("bivsDistance", "bivs_d", 2, "0: only if in the objective constraint; 1: if at distance 0 or 1; 2: any variable");
		public final int bivsLimit = addI("bivsLimit", "bivs_l", Integer.MAX_VALUE, "BIVS applied only if the domain size is <= this value");
		public final boolean optValHeuristic = addB("optValHeuristic", "ovalh", false, ""); // experimental
		public final boolean antiCBval = addB("antiCBval", "acbv", false, "Must we use anti CBval?");

		public final int stickingMode = addI("stickingMode", "stk", 0, "Must we use sticking a sticky mode (0 for none)?");
	}

	public class OptionsExtraction extends OptionGroup {
		public final Extraction method = addE("method", "e_m", Extraction.VAR, "Method for extracting unsatisfiable cores with HeadExtraction");
		public final int nCores = addI("nCores", "e_n", 1, "Number of unsatifiable cores to be extracted with HeadExtraction");
	}

	/**********************************************************************************************
	 ***** Handling user settings (from the command line, and also possibly from a file)
	 *********************************************************************************************/

	/**
	 * This class allows us to deal with options given by the user, either on the command line or by means of an XML control file
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

		/**
		 * 
		 * @param shortcut
		 *            a shortcut corresponding to tag + attribute
		 * @param tag
		 *            a tag
		 * @param att
		 *            an attribute for the tag
		 * @param defaultValue
		 *            a default value if the attribute is not present
		 * @return the value (a string) of the specified attribute for the specified tag, or the specified default value
		 */
		private String stringFor(String shortcut, String tag, String att, Object defaultValue) {
			// try first with shortcut
			String s = shortcut == null ? null : Input.argsForSolving.get(shortcut);
			if (s != null)
				return s.length() == 0 && !(defaultValue instanceof String) ? defaultValue.toString() : s;
			// try then with tag+attribute
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
			Long baseValue = Long.parseLong(Character.isDigit(lastCharacter) ? s : s.substring(0, s.length() - 1));
			double value = Character.isDigit(lastCharacter) ? baseValue
					: lastCharacter == 'k' || lastCharacter == 's' ? baseValue * 1000
							: lastCharacter == 'm' ? baseValue * 1000000 : (Double) Kit.exit("Bad character for " + tag + " " + att);
			control((longValue && Long.MIN_VALUE <= value && value <= Long.MAX_VALUE)
					|| (!longValue && Integer.MIN_VALUE <= value && value <= Integer.MAX_VALUE));
			return longValue ? (long) value : (Number) (int) value; // BE CAREFUL: problem if cast omitted
		}

		/**
		 * 
		 * @param shortcut
		 *            a shortcut corresponding to tag + attribute
		 * @param tag
		 *            a tag
		 * @param att
		 *            an attribute for the tag
		 * @param defaultValue
		 *            a default value if the attribute is not present
		 * @return the value (an int) of the specified attribute for the specified tag, or the specified default value
		 */
		private int intFor(String shortcut, String tag, String att, Integer defaultValue) {
			return (Integer) numberFor(shortcut, tag, att, defaultValue, false);
		}

		/**
		 * 
		 * @param shortcut
		 *            a shortcut corresponding to tag + attribute
		 * @param tag
		 *            a tag
		 * @param att
		 *            an attribute for the tag
		 * @param defaultValue
		 *            a default value if the attribute is not present
		 * @return the value (a long) of the specified attribute for the specified tag, or the specified default value
		 */
		private Long longFor(String shortcut, String tag, String att, Long defaultValue) {
			return (Long) numberFor(shortcut, tag, att, defaultValue, true);
		}

		/**
		 * 
		 * @param shortcut
		 *            a shortcut corresponding to tag + attribute
		 * @param tag
		 *            a tag
		 * @param att
		 *            an attribute for the tag
		 * @param defaultValue
		 *            a default value if the attribute is not present
		 * @return the value (a double) of the specified attribute for the specified tag, or the specified default value
		 */
		private double doubleFor(String shortcut, String tag, String att, Double defaultValue) {
			Double d = Utilities.toDouble(stringFor(shortcut, tag, att, defaultValue));
			control(d != null, () -> "A double value was expected for " + tag + "/" + att);
			return d;
		}

		/**
		 * 
		 * @param shortcut
		 *            a shortcut corresponding to tag + attribute
		 * @param tag
		 *            a tag
		 * @param att
		 *            an attribute for the tag
		 * @param defaultValue
		 *            a default value if the attribute is not present
		 * @return the value (a boolean) of the specified attribute for the specified tag, or the specified default value
		 */
		private boolean booleanFor(String shortcut, String tag, String att, Boolean defaultValue) {
			Boolean b = Utilities.toBoolean(stringFor(shortcut, tag, att, defaultValue));
			control(b != null, () -> "A boolean value was expected for " + tag + "/" + att);
			return b;
		}
	}

}
