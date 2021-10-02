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
import static org.xcsp.common.Constants.EMPTY_STRING;
import static org.xcsp.common.Constants.MINUS_INFINITY;
import static org.xcsp.common.Constants.PLUS_INFINITY;
import static org.xcsp.common.Constants.PLUS_INFINITY_INT;
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
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.extension.structures.Bits;
import constraints.extension.structures.Matrix.Matrix3D;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstGE;
import heuristics.HeuristicRevisions;
import heuristics.HeuristicRevisions.HeuristicRevisionsDynamic.Dom;
import heuristics.HeuristicValues;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.Wdeg;
import interfaces.Tags.TagExperimental;
import main.Head;
import main.HeadExtraction;
import optimization.ObjectiveVariable;
import optimization.Optimizer;
import propagation.GAC;
import propagation.Reviser;
import propagation.Reviser.Reviser3;
import solver.Restarter.RestarterLNS.HeuristicFreezing.Rand;
import solver.Solver;
import utility.Enums.Branching;
import utility.Enums.ConstraintWeighting;
import utility.Enums.Extension;
import utility.Enums.Extraction;
import utility.Enums.LearningIps;
import utility.Enums.LearningNogood;
import utility.Enums.OptimizationStrategy;
import utility.Enums.RestartMeasure;
import utility.Enums.SingletonStrategy;
import utility.Enums.SymmetryBreaking;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

public final class Control {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static final String SETTINGS = "settings";

	public static final String DEFAULT_SETTINGS = "defaultSettings";

	public static final String ALL = "all";

	private static final int HIDDEN = 4;

	private static final int TO_IMPLEMENT = 4;

	public static void main(String[] args) {
		Integer maximumPriority = args.length != 2 ? null : Kit.parseInteger(args[1]);
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

	private final List<Option<?>> options;

	public final UserSettings userSettings;

	public final SettingXml xml;

	public final SettingGeneral general;

	public final SettingProblem problem;

	public final SettingVars variables;

	public final SettingCtrs constraints;

	public final SettingGlobal global;

	public final SettingExtension extension;

	public final SettingOptimization optimization;

	public final SettingPropagation propagation;

	public final SettingShaving shaving;

	public final SettingLNS lns;

	public final SettingSolving solving;

	public final SettingRestarts restarts;

	public final SettingLearning learning;

	public final SettingExtraction extraction;

	public final SettingVarh varh;

	public final SettingValh valh;

	public final SettingRevh revh;

	public final SettingExperimental experimental;

	public Control(String controlFilename) {
		this.options = new ArrayList<>();
		this.userSettings = new UserSettings(controlFilename);
		this.xml = new SettingXml();
		this.general = new SettingGeneral();
		this.problem = new SettingProblem();
		this.variables = new SettingVars();
		this.constraints = new SettingCtrs();
		this.global = new SettingGlobal();
		this.extension = new SettingExtension();
		this.optimization = new SettingOptimization();
		this.propagation = new SettingPropagation();
		this.shaving = new SettingShaving();
		this.lns = new SettingLNS();
		this.solving = new SettingSolving();
		this.restarts = new SettingRestarts();
		this.learning = new SettingLearning();
		this.extraction = new SettingExtraction();
		this.varh = new SettingVarh();
		this.valh = new SettingValh();
		this.revh = new SettingRevh();
		this.experimental = new SettingExperimental();

		general.verbose = general.verbose < 1 && general.trace.length() > 0 ? 1 : general.verbose;
		control(0 <= general.verbose && general.verbose <= 3, () -> "Verbose must be in 0..3");
		Kit.log.setLevel(general.verbose == 0 ? Level.CONFIG : general.verbose == 1 ? Level.FINE : general.verbose == 2 ? Level.FINER : Level.FINEST);
		control(0 <= lns.pFreeze && lns.pFreeze < 100, () -> "percentageOfVariablesToFreeze should be between 0 and 100 (excluded)");
		control(learning.nogood != LearningNogood.RST_SYM);
		control(optimization.lb <= optimization.ub);
		controlKeys();
		if (general.exceptionsVisible)
			org.xcsp.modeler.Compiler.ev = true;
		if (general.noPrintColors)
			Kit.useColors = false;
		if (general.framework == TypeFramework.MAXCSP)
			optimization.lb = 0L;
	}

	public void controlKeys() {
		String k = Input.argsForSolving.keySet().stream().filter(key -> options.stream().noneMatch(s -> s.key().equals(key) || s.shortcut.equals(key)))
				.findFirst().orElse(null);
		control(k == null, () -> "The parameter " + k + " is unknown");
	}

	private void save(String outputFilename, int maximumPriority) {
		Document document = Kit.createNewDocument();
		Node root = document.appendChild(document.createElement(Control.SETTINGS));
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
			for (Option<?> setting : options)
				if (setting.priority != HIDDEN && setting.priority != TO_IMPLEMENT)
					System.out.print((!setting.tag.equals(tag) ? "\n  " + (tag = setting.tag) + "\n" : "") + setting);
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

		private final String tag, attribute, shortcut;

		protected final T defaultValue;

		protected T value;

		private final String description;

		private final int priority;

		private Class<?> root;

		private final String[] experimentalNames = Kit.sort(new String[] { Extraction.MAX_CSP.name(), Extraction.INC.name(), Extraction.INC_FIRST.name() });

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
			this.shortcut = shortcut;
			this.defaultValue = defaultValue;
			this.value = getValue(shortcut, tag, attribute, defaultValue);
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
						.filter(f -> f.isEnumConstant() && Arrays.binarySearch(experimentalNames, f.getName()) < 0).map(f -> f.getName()).collect(joining(" "))
						+ "\n";
			return s;
		}
	}

	private final class OptionEnum<T extends Enum<T>> extends Option<T> {

		private OptionEnum(String tag, String attribute, String shortcut, T defaultValue, String description, int... priority) {
			super(tag, attribute, shortcut, defaultValue, description, priority);
			this.value = Enum.valueOf((Class<T>) defaultValue.getClass(), userSettings.stringFor(shortcut, tag, attribute, defaultValue).toUpperCase());
		}
	}

	/**********************************************************************************************
	 * Groups of options
	 *********************************************************************************************/

	private class SettingGroup {

		private <T> Option<T> add(Option<T> option) {
			control(option.shortcut != null, () -> "A shortcut must be given");
			for (Option<?> opt : options) {
				control(!option.shortcut.equals(opt.shortcut), () -> opt.key() + " and " + option.key() + " with the same shortcut " + option.shortcut);
				control(!opt.key().equals(option.key()), () -> "The parameters " + opt.key() + " and " + option.key() + " with the same value");
			}
			options.add(option);
			return option;
		}

		protected String tag() {
			return getClass().getSimpleName().substring(0, 1).toLowerCase() + getClass().getSimpleName().substring(1);
		}

		protected int addI(String attribute, String shortcut, int defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority)).value;
		}

		protected long addL(String attribute, String shortcut, long defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority)).value;
		}

		protected double addD(String attribute, String shortcut, double defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority)).value;
		}

		protected boolean addB(String attribute, String shortcut, boolean defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority)).value;
		}

		protected String addS(String attribute, String shortcut, String defaultValue, String description, int... priority) {
			return add(new Option<>(tag(), attribute, shortcut, defaultValue, description, priority)).value;
		}

		protected String addS(String attribute, String shortcut, Class<?> defaultValue, Class<?> root, String description, int... priority) {
			String df = defaultValue == null ? "" : defaultValue.getName().substring(defaultValue.getName().lastIndexOf(".") + 1);
			root = root == null ? Reflector.getLastButOneSuperclassOf(defaultValue) : root;
			return add(new Option<String>(tag(), attribute, shortcut, df, root, description, priority)).value.trim();
		}

		protected <T extends Enum<T>> T addE(String attribute, String shortcut, T defaultValue, String description, int... priority) {
			return add(new OptionEnum<>(tag(), attribute, shortcut, defaultValue, description, priority)).value;
		}
	}

	public class SettingXml extends SettingGroup {
		public final String discardClasses = addS("discardClasses", "dc", "", "XCSP3 classes (tags) to be discarded (comma as separator)");
		public final String campaignDir = addS("campaignDir", "cd", "", "Name of a campaign directory where results (XML files) are stored.");

		// The following options determine whether special forms of intension constraints must be recognized/intercepted
		public final boolean recognizePrimitive2 = addB("recognizePrimitive2", "rp2", true, "should we attempt to recognize binary primitives?");
		public final boolean recognizePrimitive3 = addB("recognizePrimitive3", "rp3", true, "should we attempt to recognize ternary primitives?");
		public final boolean recognizeReifLogic = addB("recognizeReifLogic", "rlog", true, "should we attempt to recognize logical reification forms?");
		public final boolean recognizeExtremum = addB("recognizeExtremum", "rext", true, "should we attempt to recognize minimum/maximum constraints?");
		public final boolean recognizeSum = addB("recognizeSum", "rsum", true, "should we attempt to recognize sum constraints?");
	}

	public class SettingGeneral extends SettingGroup {
		String s_s = "The number of solutions that must be found before the solver stops." + "\n\tFor all solutions, use -s=all or -s=max.";
		String s_timeout = "The number of milliseconds that are passed before the solver stops."
				+ "\n\tYou can use the letter s as a suffix to denote seconds as e.g., -t=10s." + "\n\tFor no timeout, use -t= or -t=max.";
		String s_verbose = "Displays more or less precise information concerning the problem instance and the solution(s) found."
				+ "\n\tThe specified value must belong  in {0,1,2,3}." + "\n\tThis mode is used as follows."
				+ "\n\t0 : only some global statistics are listed ;" + "\n\t1 : in addition, solutions are  shown ;"
				+ "\n\t2 : in addition, additionnal information about the problem instance to be solved is given ;"
				+ "\n\t3 : in addition, for each constraint, allowed or unallowed tuples are displayed.";

		public TypeFramework framework = null;
		public long nSearchedSolutions = addL("nSearchedSolutions", "s", -1, s_s); // -1 when not initialized
		public final long timeout = addL("timeout", "t", PLUS_INFINITY, s_timeout);
		public int verbose = addI("verbose", "v", 0, s_verbose);
		public int jsonLimit = addI("jsonLimit", "jsonLimit", 1000, "");
		public final boolean jsonAux = addB("jsonAux", "jsonAux", false, "");
		public boolean xmlCompact = addB("xmlCompact", "xmlCompact", true, "");
		public boolean xmlAllSolutions = addB("xmlAllSolutions", "xas", false, "");

		public final String trace = addS("trace", "trace", EMPTY_STRING, "Displays a trace (with possible depth control as eg -trace=10-20");
		public final long seed = addL("seed", "seed", 0, "The seed that can be used for some random-based methods.");
		public final boolean exceptionsVisible = addB("exceptionsVisible", "ev", false, "Makes exceptions visible.");
		public final boolean enableAnnotations = addB("enableAnnotations", "ea", false, "Enables annotations (currently, mainly concerns priority variables).");
		public final int satisfactionLimit = addI("satisfactionLimit", "sal", PLUS_INFINITY_INT, "converting the objective into a constraint with this limit");
		public final boolean recordSolutions = addB("recordSolutions", "rs", false, "Records all found solutions", HIDDEN);
		public final boolean noPrintColors = addB("noPrintColors", "npc", false, "Don't use special color characters in the terminal", HIDDEN);

		public void decideFramework(Optimizer optimizer) {
			control(framework == null);
			if (optimizer != null) { // to COP
				if (nSearchedSolutions == -1)
					nSearchedSolutions = PLUS_INFINITY; // default value for COP (in order to find an optimum)
				framework = TypeFramework.COP;
				if (optimizer.ctr instanceof ObjectiveVariable || optimizer.ctr instanceof MaximumCstLE || optimizer.ctr instanceof MinimumCstGE)
					restarts.restartAfterSolution = true;
			} else {
				if (nSearchedSolutions == -1)
					nSearchedSolutions = 1; // default value for CSP
				framework = TypeFramework.CSP;
			}
		}
	}

	public class SettingProblem extends SettingGroup {
		public final String data = addS("data", "data", "", "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName());
		public final String variant = addS("variant", "variant", "", "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName());
		public final boolean shareBitVectors = addB("shareBitVectors", "sbv", false, "Trying to save space by sharing bit vectors.", HIDDEN);
		public final SymmetryBreaking symmetryBreaking = addE("symmetryBreaking", "sb", SymmetryBreaking.NO,
				"Symmetry-breaking method (requires Saucy to be installed");

		public boolean isSymmetryBreaking() {
			return symmetryBreaking != SymmetryBreaking.NO;
		}
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

		protected final String selection = addS("selection", "sel", EMPTY_STRING, s_sel);
		protected final String instantiation = addS("instantiation", "ins", EMPTY_STRING, s_ins);
		protected final String priority1 = addS("priority1", "pr1", EMPTY_STRING, s_pr1);
		protected final String priority2 = addS("priority2", "pr2", EMPTY_STRING, s_pr2);
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
					Integer num = Kit.parseInteger(token);
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
			return Kit.sort(set.toArray(new Object[set.size()]));
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
			Object[] t = Kit.concat(instantiatedVars, priority1Vars, priority2Vars);
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

	public class SettingCtrs extends SettingGroup {
		String r2 = "When > 0, redundant allDifferent constraints are sought (at most as the given value) and posted (if any) to improve the filtering capability of the solver."
				+ "\n\tTry this on a pigeons instance.";
		String r5 = "Create Permutation constraints instead of classic AllDifferent when possible. Less filtering but may be faster.";

		public final boolean preserve1 = addB("preserve1", "pc1", true, "Must we keep unary constraints (instead of filtering them straight)");
		public final int decomposeIntention = addI("decomposeIntention", "di", 1, "0: no decomposition, 1: conditional decomposition, 2: forced decompostion");
		public final boolean viewForSum = addB("viewForSum", "vs", false, "");
		public final boolean intensionToExtension1 = addB("intensionToExtension1", "ie1", true,
				"Must we convert unary intension constraints into extension ones?");
		public final TypeCtr ignoredType = Types.valueOf(TypeCtr.class, addS("ignoreType", "ignoreType", "", "Ignore all constraints of this type."));
		public final int ignoreArity = addI("ignoreArity", "ignoreArity", -1, "Ignore all constraints with this arity.");

		public final int inferAllDifferentNb = addI("inferAllDifferentNb", "iad", 0, r2);
		public final int inferAllDifferentSize = addI("inferAllDifferentSize", "iadsz", 5, "Size under which inferred AllDifferent are no more considered");
		public final boolean recognizePermutations = addB("recognizePermutations", "perm", false, r5);
		public final int positionsLb = addI("positionsLb", "poslb", 3, "Minimal arity to build the array positions");
		public final int positionsUb = addI("positionsUb", "posub", 10000, "maximal number of variables to build the array positions");
	}

	public class SettingGlobal extends SettingGroup {
		String s = "Allows the user to select the propagator for ";

		public final int typeAllDifferent = addI("typeAllDifferent", "g_ad", 0, s + "allDifferent");
		public final int typeDistinctVectors = addI("typeDistinctVectors", "g_dv", 0, s + "distinctvectors");
		public final int typeAllEqual = addI("typeAllEqual", "g_ae", 0, s + "allEqual");
		public final int typeNotAllEqual = addI("typeNotAllEqual", "g_nae", 0, s + "notAllEqual");
		public final int typeOrdered = addI("typeOrdered", "g_ord", 1, s + "odered");
		public final int typeNoOverlap = addI("typeNoOverlap", "g_no", 0, s + "noOverlap");
		public final boolean redundNoOverlap = addB("redundNoOverlap", "r_no", true, "");
		public final int typeBinpacking = addI("typeBinpacking", "g_bp", 0, s + "binPacking");

		public final boolean starred = addB("starred", "starred", false, "When true, some global constraints are encoded by starred tables");
		public final boolean hybrid = addB("hybrid", "hybrid", false, "When true, some global constraints are encoded by hybrid/smart tables");
	}

	public class SettingExtension extends SettingGroup {
		public final Extension positive = addE("positive", "positive", Extension.CT, "Algorithm for (non-binary) positive table constraints");
		public final Extension negative = addE("negative", "negative", Extension.V, "Algorithm for (non-binary) negtaive table constraint");
		public final boolean validForBinary = addB("validForBinary", "vfor2", true, "");
		public final String structureClass2 = addS("structureClass2", "sc2", Bits.class, null, "Structures to be used for binary table constraints");
		public final String structureClass3 = addS("structureClass3", "sc3", Matrix3D.class, null, "Structures to be used for ternary table constraints");
		public final int arityLimitForSwitchingToPositive = addI("arityLimitForSwitchingToPositive", "ntop", -1, "");
		public final int arityLimitForSwitchingToNegative = addI("arityLimitForSwitchingToNegative", "pton", -1, "");
		public final boolean decremental = addB("decremental", "exd", true, ""); // true required for CT for the moment
		public final int variant = addI("variant", "exv", 0, "");

		public final int arityLimitForConvertingIntension = addI("arityLimitForConvertingIntension", "alc", 0, "");
		public final int spaceLimitForConvertingIntension = addI("spaceLimitForConvertingIntension", "plc", 20, "");

		public boolean mustReverse(int arity, boolean positive) {
			return (positive && arity <= arityLimitForSwitchingToNegative) || (!positive && arity <= arityLimitForSwitchingToPositive);
		}

		public boolean convertingIntension(Variable[] vars) {
			return vars.length <= arityLimitForConvertingIntension
					&& Constraint.howManyVariablesWithin(vars, spaceLimitForConvertingIntension) == Constants.ALL;
		}
	}

	public class SettingOptimization extends SettingGroup {
		public long lb = addL("lb", "lb", MINUS_INFINITY, "initial lower bound");
		public long ub = addL("ub", "ub", PLUS_INFINITY, "initial upper bound");
		public final OptimizationStrategy strategy = addE("strategy", "os", OptimizationStrategy.DECREASING, "optimization strategy");
	}

	public class SettingPropagation extends SettingGroup {
		String s_uaq = "If enabled, queues of constraints are used in addition to the queue of variables. The purpose is to propagate less often the most costly constraints.";

		public String clazz = addS("clazz", "p", GAC.class, null, "Class to be used for propagation (for example, FC, GAC or SAC3)");
		public final int variant = addI("variant", "pv", 0, "Propagation Variant (only used for some consistencies)", HIDDEN);
		public final boolean useAuxiliaryQueues = addB("useAuxiliaryQueues", "uaq", false, s_uaq);
		public final String reviser = addS("reviser", "reviser", Reviser3.class, Reviser.class, "class to be used for performing revisions");
		public boolean residues = addB("residues", "res", true, "Must we use redidues (GAC3rm)?");
		public boolean bitResidues = addB("bitResidues", "bres", true, "Must we use bit resides (GAC3bit+rm)?");
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

	public class SettingExtraction extends SettingGroup {
		String s = "\n\tValid only with the command: java " + HeadExtraction.class.getName();

		public final Extraction method = addE("method", "e_m", Extraction.VAR, "method for extracting unsatisfiable cores." + s);
		public final int nCores = addI("nCores", "e_nc", 1, "number of unsatifiable cores to be extracted." + s);
	}

	public class SettingVarh extends SettingGroup {
		public final String heuristic = addS("heuristic", "varh", Wdeg.class, HeuristicVariables.class, "class of the variable ordering heuristic");
		public final boolean anti = addB("anti", "anti_varh", false, "must we follow the anti heuristic?");
		public int lc = addI("lc", "lc", 2, "value for lc (last conflict); 0 if not activated");
		public final ConstraintWeighting weighting = addE("weighting", "wt", ConstraintWeighting.CACD, "how to manage weights for wdeg variants");
		public final SingletonStrategy singleton = addE("singleton", "sing", SingletonStrategy.LAST, "how to manage singleton variables during search");
		public final boolean discardAux = addB("discardAux", "da", false, "must we discard auxiliary variables introduced by the solver?");
	}

	public class SettingValh extends SettingGroup {
		public final String clazz = addS("clazz", "valh", First.class, HeuristicValues.class, "class of the value ordering heuristic");
		public final boolean anti = addB("anti", "anti_valh", false, "reverse of the natural heuristic order?");
		public final boolean runProgressSaving = addB("runProgressSaving", "rps", false, "run progress saving");
		public final int solutionSaving = addI("solutionSaving", "sos", 1, "solution saving (0 disabled, 1 enabled, otherwise desactivation period");
		public final String warmStart = addS("warmStart", "warm", "", "a starting instantiation (solution) to be used with solution saving");

		public boolean bivsStoppedAtFirstSolution = addB("bivsStoppedAtFirstSolution", "bivs_s", true, "");
		public boolean bivsOptimistic = addB("bivsOptimistic", "bivs_o", true, "");
		public final int bivsDistance = addI("bivsDistance", "bivs_d", 2, "0: only if in the objective constraint; 1: if at distance 0 or 1; 2: any variable");
		public final int bivsLimit = addI("bivsLimit", "bivs_l", Integer.MAX_VALUE,
				"MAX_VALUE means no control/limit; otherwise bivs applied only if the domain size is <= bivsl");
		public final boolean optValHeuristic = addB("optValHeuristic", "ovh", false, "");
	}

	public class SettingRevh extends SettingGroup {
		public final String clazz = addS("clazz", "revh", Dom.class, HeuristicRevisions.class, "class of the revision ordering heuristic");
		public final boolean anti = addB("anti", "anti_revh", false, "reverse of the natural heuristic order?");
	}

	public class SettingExperimental extends SettingGroup {
		public int testI1 = addI("testI1", "testI1", 0, "", HIDDEN);
		public int testI2 = addI("testI2", "testI2", 0, "", HIDDEN);
		public int testI3 = addI("testI3", "testI3", 0, "", HIDDEN);
	}

	/**********************************************************************************************
	 ***** Handling user settings (from the command line, and also possibly from a file)
	 *********************************************************************************************/

	public class UserSettings {

		public static final String MIN = "min";
		public static final String MAX = "max";

		private Document document;

		private XPath xPath;

		public final String controlFilename;

		private UserSettings(String controlFilename) {
			this.controlFilename = controlFilename != null ? controlFilename : Input.controlFilename;
			if (controlFilename != null && !controlFilename.equals(Control.DEFAULT_SETTINGS)) {
				// Loads the XML file containing all settings from the user.
				document = Kit.load(new File(controlFilename));
				xPath = XPathFactory.newInstance().newXPath();
			}
		}

		/** Returns the value (a String) of the specified attribute for the specified tag. */
		private String stringFor(String shortcut, String tag, String att, Object defaultValue) {
			// try with shortcut
			String value = shortcut == null ? null : Input.argsForSolving.get(shortcut);
			if (value != null)
				return value.length() == 0 && !(defaultValue instanceof String) ? defaultValue.toString() : value;
			// try with tag+attribute
			value = Input.argsForSolving.get((tag != null ? tag + "/" : "") + att);
			if (value != null)
				return value;
			if (document == null)
				return defaultValue.toString();
			// try in document
			try {
				NodeList nodes = (NodeList) xPath.compile("//" + (tag != null ? tag : "*") + "/@" + att).evaluate(document, XPathConstants.NODESET);
				control(nodes.getLength() <= 1, () -> "Problem with several possibilities for " + tag + " " + att);
				if (nodes.getLength() == 0)
					return defaultValue.toString();
				value = nodes.item(0).getNodeValue();
				return value.length() == 0 && !(defaultValue instanceof String) ? defaultValue.toString() : value;
			} catch (XPathExpressionException e) {
				Kit.exit("problem xpath", e);
			}
			return (String) Kit.exit("Problem with " + tag + " and " + att + " and " + defaultValue);
		}

		private Number numberFor(String shortcut, String tag, String att, Object defaultValue, boolean longValue) {
			String s = stringFor(shortcut, tag, att, defaultValue).toLowerCase();
			if (s.equals(MIN))
				return longValue ? Long.MIN_VALUE : (Number) Integer.MIN_VALUE; // problem if cast omitted
			if (s.equals(MAX) || s.equals(Control.ALL))
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
