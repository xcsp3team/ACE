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
import static org.xcsp.common.Constants.MINUS_INFINITY;
import static org.xcsp.common.Constants.PLUS_INFINITY;
import static org.xcsp.common.Constants.PLUS_INFINITY_INT;

import java.io.File;
import java.lang.reflect.Field;
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
import org.xcsp.common.Types.TypeCtr;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;

import constraints.extension.structures.Bits;
import constraints.extension.structures.Matrix3D;
import heuristics.HeuristicRevisions;
import heuristics.HeuristicRevisions.HeuristicRevisionsDirect.First;
import heuristics.HeuristicRevisions.HeuristicRevisionsDirect.Last;
import heuristics.HeuristicRevisions.HeuristicRevisionsDynamic.Dom;
import heuristics.HeuristicValues;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import interfaces.Tags.TagExperimental;
import interfaces.Tags.TagInvisible;
import main.Head;
import main.HeadExtraction;
import propagation.GAC;
import propagation.QueueForSAC3.CellIterator;
import propagation.Reviser;
import propagation.Reviser.Reviser3;
import solver.Restarter.RestarterLB.LocalBranchingConstraint.LBAtMostDistanceSum;
import solver.Restarter.RestarterLNS.HeuristicFreezing.Rand;
import solver.SolutionManager;
import solver.backtrack.SolverBacktrack;
import solver.local.HeuristicNeighbors.BestGlobal;
import solver.local.TabuManager.TabuManagerVariableValue;
import utility.DocumentHandler;
import utility.Enums.EBinaryEncoding;
import utility.Enums.EBranching;
import utility.Enums.EExtension;
import utility.Enums.EExtractionMethod;
import utility.Enums.ELearningNogood;
import utility.Enums.ELearningState;
import utility.Enums.EOptimizationStrategy;
import utility.Enums.ERestartsMeasure;
import utility.Enums.ESingletonAssignment;
import utility.Enums.ESymmetryBreaking;
import utility.Enums.EWeighting;
import utility.Kit;
import utility.Reflector;

public class Control {

	public final String settingsFilename = staticUserSettingsFilename;

	public final ControlPanelSettings settings = new ControlPanelSettings(settingsFilename);

	/**********************************************************************************************
	 * Fields for control panel settings
	 *********************************************************************************************/

	class SettingGroup {

		protected static final int HIDDEN = 4;
		protected static final int TO_IMPLEMENT = 4;

		protected String tag() {
			return getClass().getSimpleName().substring(0, 1).toLowerCase() + getClass().getSimpleName().substring(1);
		}

		private int pr(int[] t) {
			return t.length == 0 ? 1 : t.length == 1 ? t[0] : (Integer) Kit.exit("Only zero or one priority value expected");
		}

		protected int addI(String attribute, String shortcut, int defaultValue, String description, int... priority) {
			return settings.addI(pr(priority), tag(), attribute, shortcut, defaultValue, description);
		}

		protected long addL(String attribute, String shortcut, long defaultValue, String description, int... priority) {
			return settings.addL(pr(priority), tag(), attribute, shortcut, defaultValue, description);
		}

		protected double addD(String attribute, String shortcut, double defaultValue, String description, int... priority) {
			return settings.addD(pr(priority), tag(), attribute, shortcut, defaultValue, description);
		}

		protected boolean addB(String attribute, String shortcut, boolean defaultValue, String description, int... priority) {
			return settings.addB(pr(priority), tag(), attribute, shortcut, defaultValue, description);
		}

		protected String addS(String attribute, String shortcut, String defaultValue, String description, int... priority) {
			return settings.addS(pr(priority), tag(), attribute, shortcut, defaultValue, description);
		}

		protected String addS(String attribute, String shortcut, Class<?> defaultValue, Class<?> root, String description, int... priority) {
			return settings.addS(pr(priority), tag(), attribute, shortcut, defaultValue, root, description);
		}

		private Class<?> getLastButOneSuperclassOf(Class<?> clazz) {
			for (Class<?> superclass = clazz.getSuperclass(); superclass != Object.class; superclass = superclass.getSuperclass())
				clazz = superclass;
			return clazz;
		}

		protected String addS(String attribute, String shortcut, Class<?> defaultValue, String description, int... priority) {
			return addS(attribute, shortcut, defaultValue, getLastButOneSuperclassOf(defaultValue), description);
		}

		protected <T extends Enum<T>> T addE(String attribute, String shortcut, T defaultValue, String description, int... priority) {
			return settings.addE(pr(priority), tag(), attribute, shortcut, defaultValue, description);
		}
	}

	public class SettingXml extends SettingGroup {
		String s_dc = "Names of classes (tags) to discard (use comma as separator if several classes). Effective iff an XCSP3 file is loaded.";
		String s_cm = "Output made compatible with XCSP3 competitions";
		String s_dir = "Indicates the name of a directory where results (XML files) for a campaign will be stored."
				+ "\n\tIf the value is the empty string, results are not saved.";
		String s_kin = "When saving in XCSP3, indicates if the initial name of the instance must be preserved.";
		String s_iag = "When compiling to XCSP3, avoids to build groups automatically";
		String s_sis = "When compiling to XCSP3, avoids to group constraints that are separated";
		String s_dpri = "Displays recognized primitives, at parsing time";

		public final String discardedClasses = addS("discardedClasses", "dc", EMPTY_STRING, s_dc);
		public final boolean competitionMode = addB("competitionMode", "cm", true, s_cm);
		public final String dirForCampaign = addS("dirForCampaign", "dir", EMPTY_STRING, s_dir);
		public final boolean keepInstanceName = addB("keepInstanceName", "kin", false, s_kin, HIDDEN);
		public final boolean ignoreAutomaticGroups = addB("ignoreAutomaticGroups", "iag", false, s_iag, HIDDEN);
		public final boolean saveImmediatelyStored = addB("saveImmediatelyStored", "sis", true, s_sis, HIDDEN);
		public final boolean displayPrimitives = addB("displayPrimitives", "dpri", false, s_dpri, HIDDEN);
	}

	public final SettingXml settingXml = new SettingXml();

	public class SettingGeneral extends SettingGroup {
		String s_framework = "The kind of problem instance to be solved (the specified value is case-insensitive).";
		String s_s = "The number of solutions that must be found before the solver stops." + "\n\tFor all solutions, use -s=all or -s=max.";
		String s_timeout = "The number of milliseconds that are passed before the solver stops."
				+ "\n\tYou can use the letter s as a suffix to denote seconds as e.g., -t=10s." + "\n\tFor no timeout, use -t= or -t=max.";
		String s_verbose = "Displays more or less precise information concerning the problem instance and the solution(s) found."
				+ "\n\tThe specified value must belong  in {0,1,2,3}." + "\n\tThis mode is used as follows."
				+ "\n\t0 : only some global statistics are listed ;" + "\n\t1 : in addition, solutions are  shown ;"
				+ "\n\t2 : in addition, additionnal information about the problem instance to be solved is given ;"
				+ "\n\t3 : in addition, for each constraint, allowed or unallowed tuples are displayed.";
		String s_trace = "Displays every decision taken during search with -trace."
				+ "\n\tYou can control the trace with a required min depth and/or max depth as eg -trace=10-20.";
		String s_seed = "The seed that can be used for some random-based methods.";
		String s_ev = "Makes exceptions visible.";
		String s_ea = "Enables annotations (currently, mainly concerns priority variables).";
		String l_cfs = "Only valid if a COP is loaded and if the framework is set to CSP by the user."
				+ "\n\tIn that case, the objective is turned into a constraint specified by this limit.";
		String s_cfs = "Only valid if a COP is loaded and if the framework is set to CSP by the user."
				+ "\n\tIn that case, the objective is turned into a constraint specified by this condition."
				+ "\t The condition has the form (operator,value) as e.g., (lt,10). Currently, not operative, so must be implemented for XCSP3";
		String s_rs = "Records all found solutions in a list of " + SolutionManager.class.getName();

		public TypeFramework framework = addE("framework", "f", TypeFramework.CSP, s_framework);
		public long nSearchedSolutions = addL("nSearchedSolutions", "s", framework == TypeFramework.CSP ? 1 : PLUS_INFINITY, s_s);
		public final long timeout = addL("timeout", "t", PLUS_INFINITY, s_timeout);
		public final int verbose = addI("verbose", "v", 1, s_verbose);
		public final String trace = addS("trace", "trace", EMPTY_STRING, s_trace);
		public final long seed = addL("seed", "seed", 0, s_seed);
		public final boolean makeExceptionsVisible = addB("makeExceptionsVisible", "ev", false, s_ev);
		public final boolean enableAnnotations = addB("enableAnnotations", "ea", false, s_ea);
		public final int limitForSatisfaction = addI("limitForSatisfaction", "lfs", PLUS_INFINITY_INT, l_cfs);
		public final String conditionForSatisfaction = addS("conditionForSatisfaction", "cfs", EMPTY_STRING, s_cfs, TO_IMPLEMENT);
		public final boolean recordSolutions = addB("recordSolutions", "rs", false, s_rs, HIDDEN);
		public final String saveNetworkGraph = addS("saveNetworkGraph", "sng", EMPTY_STRING,
				"Three bits indicating if we need respectively a macro, positive and primal graph");
	}

	public final SettingGeneral settingGeneral = new SettingGeneral();

	public void toCSP() {
		settingGeneral.framework = TypeFramework.CSP;
		settingGeneral.nSearchedSolutions = 1;
	}

	public void toCOP() {
		settingGeneral.framework = TypeFramework.COP;
		settingGeneral.nSearchedSolutions = PLUS_INFINITY;
	}

	public class SettingProblem extends SettingGroup {
		String s_data = "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName();
		String s_dataFormat = "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName();
		String s_dataexport = "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName();
		String s_variant = "Parameter similar to the one defined for " + org.xcsp.modeler.Compiler.class.getName();

		String s_sb = "Allows us to post (if possible) symmetry breaking constraints using the method described in [Lecoutre and Tabary 2009]."
				+ "\n\tSaucy is required to run the different methods.";
		String s_sbv = "Try to save space by sharing bit vectors.";
		String s_cg = "Add binary constraints to get a complete constraint graph.";

		String s_be = "Transforms a CN only involving (non-binary) extensional constraints into a binary CN."
				+ "\n\tCurrently, only works for XCSP2. To be implemented for XCSP3 for just the hidden encoding.";

		public final String data = addS("data", "data", EMPTY_STRING, s_data);
		public final String dataFormat = addS("dataFormat", "dataFormat", EMPTY_STRING, s_dataFormat);
		public final boolean dataexport = addB("dataexport", "dataexport", false, s_dataexport);
		public final String variant = addS("variant", "variant", EMPTY_STRING, s_variant);

		public final boolean shareBitVectors = addB("shareBitVectors", "sbv", false, s_sbv, HIDDEN);
		public final boolean completeGraph = addB("completeGraph", "cg", false, s_cg, HIDDEN); // used for PC8
		public final EBinaryEncoding binaryEncoding = addE("binaryEncoding", "be", EBinaryEncoding.NO, s_be, TO_IMPLEMENT);

		public final ESymmetryBreaking symmetryBreaking = addE("symmetryBreaking", "sb", ESymmetryBreaking.NO, s_sb);

		public boolean isSymmetryBreaking() {
			return symmetryBreaking != ESymmetryBreaking.NO;
		}
	}

	public final SettingProblem settingProblem = new SettingProblem();

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
		String s_riv = "When set to true, only keep one arbitrary value in the domain of each variable involved in no constraint.";

		protected final String selection = addS("selection", "sel", EMPTY_STRING, s_sel);
		protected final String instantiation = addS("instantiation", "ins", EMPTY_STRING, s_ins);
		protected final String priority1 = addS("priority1", "pr1", EMPTY_STRING, s_pr1);
		protected final String priority2 = addS("priority2", "pr2", EMPTY_STRING, s_pr2);
		public final boolean reduceIsolatedVars = addB("reduceIsolatedVars", "riv", true, s_riv);

		//
		private Object[] readSelectionList(String s) {
			if (s == null || s.trim().length() == 0)
				return new Object[0];
			String msg = "Badly formed list. For example, you cannot mix ids and numbers of variables in the same list.";
			Set<Object> set = new HashSet<>();
			for (String token : s.split(",")) {
				if (token.contains("..")) {
					Kit.control(token.matches("-?\\d+\\.\\.\\d+"), () -> msg + " Pb with " + token);
					Kit.control(set.isEmpty() || set.iterator().next() instanceof Integer, () -> msg);
					int[] t = Utilities.toIntegers(token.split("\\.\\."));
					for (int num = Math.abs(t[0]); num <= t[1]; num++)
						if (t[0] >= 0)
							set.add(num);
						else
							set.remove(num);
				} else {
					Integer num = Kit.parseInteger(token);
					if (num != null) {
						Kit.control(set.isEmpty() || set.iterator().next() instanceof Integer, () -> msg);
						if (num >= 0)
							set.add(num);
						else
							set.remove(-num);
					} else {
						Kit.control(set.isEmpty() || set.iterator().next() instanceof String, () -> msg);
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
			Kit.control(t.length == 2, () -> instantiation);
			return left ? readSelectionList(t[0]) : Utilities.toIntegers(t[1].split(","));
		}

		private Object[] controlAndFinalizeVariablesLists(Object[] priority1Vars, Object[] priority2Vars) {
			// Selected variables are only valid for XCSP
			// control about instantiatedVars and instantiatedVals is made in addUnaryConstraintsOfUserInstantiation of Problem
			Object[] t = Kit.concat(instantiatedVars, priority1Vars, priority2Vars);
			if (t.length > 0) {
				Kit.control(Stream.of(t).distinct().count() == t.length, () -> "Two variables are identical in your lists (-sel -pr1 -pr2)");
				Kit.control(selectedVars.length == 0 || Stream.of(t).allMatch(o -> Arrays.binarySearch(selectedVars, o) >= 0),
						() -> "One variable present in one of your list -ins -pr1 or -pr2 is not present in your selection (-sel).");
			}
			return t;
		}

		// either nums of selected variables or ids of selected variables
		public final Object[] selectedVars = readSelectionList(selection);;

		// either nums of instantiated variables or ids of instantiated variables
		public final Object[] instantiatedVars = (Object[]) splitSelection(true);

		public final int[] instantiatedVals = (int[]) splitSelection(false);

		private final Object[] priority1Vars = readSelectionList(priority1), priority2Vars = readSelectionList(priority2);

		public final Object[] priorityVars = controlAndFinalizeVariablesLists(priority1Vars, priority2Vars);

		public final int nStrictPriorityVars = instantiatedVars.length + priority1Vars.length;
	}

	public final SettingVars settingVars = new SettingVars();

	public class SettingCtrs extends SettingGroup {
		String s_ignoreType = "Ignore all constraints of this type. Works for XCSP3";
		String s_ignoreArity = "Ignore all constraints of this arity. Works for XCSP3";

		String r2 = "When > 0, redundant allDifferent constraints are sought (at most as the given value) and posted (if any) to improve the filtering capability of the solver."
				+ "\n\tTry this on a pigeons instance.";
		String r5 = "Create Permutation constraints instead of classic AllDifferent when possible. Less filtering but may be faster.";

		public boolean preserveUnaryCtrs = addB("preserveUnaryCtrs", "puc", true, "");
		public final TypeCtr ignoredCtrType = org.xcsp.common.Types.valueOf(TypeCtr.class, addS("ignoreCtrType", "ignoreType", "", s_ignoreType));
		public final int ignoreCtrArity = addI("ignoreCtrArity", "ignoreArity", -1, s_ignoreArity);
		public boolean ignorePrimitives = addB("ignorePrimitives", "ip", false, "");

		public final int inferAllDifferentNb = addI("inferAllDifferentNb", "iad", 0, r2);
		public final int inferAllDifferentSize = addI("inferAllDifferentSize", "iadsz", 5, "");
		public final boolean recognizePermutations = addB("recognizePermutations", "perm", false, r5);
		public final boolean recognizeBoundOrientedCtrs = addB("recognizeBoundOrientedCtrs", "boc", false, ""); // TODO control this
		public final int recognizeBoundOrientedCtrsLimit = addI("recognizeBoundOrientedCtrLimit", "bocl", 300, "");
		public final int arityLimitForVapArrayLb = addI("arityLimitForVapArrayLb", "alvalb", 2, "");
		public final int arityLimitForVapArrayUb = addI("arityLimitForVapArrayUb", "alvaub", 100000, "");

		public boolean normalizeCtrs = addB("normalizeCtrs", "nc", false, "Merging constraints of similar scope (when possible)", TO_IMPLEMENT);
	}

	public final SettingCtrs settingCtrs = new SettingCtrs();

	public class SettingGlobal extends SettingGroup {
		String s1 = "Type 0 for propagators will be the priority choice in case of export.";
		String s = "Allows the user to select the propagator for ";

		String r1 = "When set to yes, some global constraints are encoded into classical table constraintss.";
		String r2 = "When set to yes, some global constraints are encoded into joker table constraintss.";
		String r3 = "When set to yes, some global constraints are encoded into smart table constraints.";

		public final boolean priorityType0 = addB("priorityType0", "g_pt0", true, s1);
		public final int typeAllDifferent = addI("typeAllDifferent", "g_ad", 0, s + "allDifferent");
		public final int typeDistinctVectors2 = addI("typeDistinctVectors2", "g_dv2", 0, s + "distinctvectors2");
		public final int typeDistinctVectorsK = addI("typeDistinctVectorsK", "g_dvk", 1, s + "distinctVectorsK");
		public final int typeAllDifferentMatrix = addI("typeAllDifferentMatrix", "g_adm", 1, s + "allDifferentMatrix");
		public final int typeAllEqual = addI("typeAllEqual", "g_ae", 0, s + "allEqual");
		public final int typeNotAllEqual = addI("typeNotAllEqual", "g_nae", 0, s + "notAllEqual");
		public final int typeInstantiation = addI("typeInstantiation", "g_ins", 1, s + "instantiation");
		public final int typeClause = addI("typeClause", "g_cla", 1, s + "clause");
		public final int typeOrdered = addI("typeOrdered", "g_ord", 1, s + "odered");
		public final int typeNoOverlap = addI("typeNoOverlap", "g_no", 0, s + "noOverlap");

		public final boolean basicTable = addB("basicTable", "bt", false, r1);
		public final boolean jokerTable = addB("jokerTable", "jt", false, r2);
		public final boolean smartTable = addB("smartTable", "st", false, r3);
	}

	public final SettingGlobal settingGlobal = new SettingGlobal();

	public class SettingExtension extends SettingGroup {
		String s_positive = "For (non-binary) constraints defined in extension, there are many ways of representing and propagating them."
				+ "\n\tWe have v for GAC-valid, a for GAC-allowed, va for GAC-valid+allowed, str1 for simple tabular reduction, str2 and mdd...";
		String s_negative = "For non-binary constraints defined in extension, representation of negative table constraints...";
		String s_ma = "Indicates whether we must use the algorithm apriori for mining items in tables.";
		String s_mt = "The threshold used for the selected mining technique.";
		String s_wcnc = "When an instance is aimed at being saved in XCSP format, it is possible to convert a CN (in extensional form) into a WCN one."
				+ "\n\tIf the value of this parameter is RANDOM, then random costs are generated:"
				+ "\n\t a) positive table : for supports (in table; random cost between [0,...,k-1] and defaultCost=k."
				+ "\n\tb) negative table : for conflicts (in table; random cost between [1,...,k] and defaultCost=0."
				+ "\n\tIf the value of this parameter is NATURAL, supports have cost 0 and conflicts have cost 1."
				+ "\n\tNote that is is only currently implemented for instances with extensional constraints.";

		public final EExtension positive = addE("positive", "positive", EExtension.CT, s_positive);
		public final EExtension negative = addE("negative", "negative", EExtension.V, s_negative);
		public final boolean validForBinary = addB("validForBinary", "vfor2", true, "");
		public final String classForBinaryExtensionStructure = addS("classForBinaryExtensionStructure", "cfor2", Bits.class, "");
		public final String classForTernaryExtensionStructure = addS("classForTernaryExtensionStructure", "cfor3", Matrix3D.class, "");
		public final int arityLimitForSwitchingToPositive = addI("arityLimitForSwitchingToPositive", "ntop", -1, "");
		public final int arityLimitForSwitchingToNegative = addI("arityLimitForSwitchingToNegative", "pton", -1, "");
		public final boolean decremental = addB("decremental", "exd", true, ""); // true required for CT for the moment
		public final int variant = addI("variant", "exv", 0, "");

		public final int arityLimitForIntensionToExtension = addI("arityLimitForIntensionToExtension", "aie", 0, "");
		public final long validLimitForIntensionToExtension = addL("validLimitForIntensionToExtension", "vie", 2000000L, "");

		public final boolean miningApriori = addB("miningApriori", "ma", false, s_ma, HIDDEN);
		public double miningThreshold = addD("miningThreshold", "mt", 0.1, s_mt, HIDDEN);

		public boolean mustReverse(int arity, boolean positive) {
			return (positive && arity <= arityLimitForSwitchingToNegative) || (!positive && arity <= arityLimitForSwitchingToPositive);
		}
	}

	public final SettingExtension settingExtension = new SettingExtension();

	public class SettingOptimization extends SettingGroup {
		String s_lb = "The specified value indicates the initial lower bound. When the solver gets a solution less than or equal to this value, it stops.";
		String s_ub = "The specified value indicates the initial upper bound."
				+ "\n\tFor a WCSP instance, this is the initial forbidden cost (allowed maximal cost plus one).";
		String s_os = "For COP, the way bound intervals are managed.";
		String s_ct = "For WCSP, the way cost transferts are managed.";
		String s_astr = "The specified value indicates the arity that determines the use of Soft STR constraints (if required by other configuration parameters; for a WCSP instance.";
		String s_estr = "The specified value indicates if GAC or GACw is enforced for Soft STR constraints, for a WCSP instance.";

		public long lowerBound = addL("lowerBound", "lb", settingGeneral.framework == TypeFramework.MAXCSP ? 0L : MINUS_INFINITY, s_lb);
		public long upperBound = addL("upperBound", "ub", PLUS_INFINITY, s_ub);
		public final EOptimizationStrategy optimizationStrategy = addE("optimizationStrategy", "os", EOptimizationStrategy.DECREASING, s_os);
		// public final ECostTranfer costTranfer = addE("costTranfer", "ct", ECostTranfer.INVARIABLE, s_ct);
	}

	public final SettingOptimization settingOptimization = new SettingOptimization();

	public class SettingPropagation extends SettingGroup {
		String s_p = "The name of the class used to propagate constraints."
				+ "\n\tFor (G)AC, use AC. Among other possible values, we find SAC1, SAC3, ESAC3, CDC1, CPC1, DC1, DC2.";
		String s_pv = "Variant for a second order consistency";
		String s_uaq = "If enabled, queues of constraints are used in addition to the queue of variables. The purpose is to propagate less often the most costly constraints.";
		String s_rm = "The name of the class used to perform revisions.";

		String r1 = "Determines if residues must be exploited." + "\n\tFor CSP, that corresponds to use either (G)AC3 or (G)AC3rm";
		String r2 = "Determines if bit residues must be exploited.";

		String q1 = "For intension constraints, control the effort for (G)AC."
				+ "\n\tGAC is not enforced if the current number of future variables is more than the specified value.";

		String q2 = "For intension constraints, control the effort for (G)AC."
				+ "\n\tGAC is not enforced if the size of the current Cartesian product is more than than 2 up the specified value.";
		String q3 = "For intension constraints, GAC is guaranteed to be enforced if the arity is not more than the specified value.";

		public String clazz = addS("clazz", "p", GAC.class, s_p);
		public final int variant = addI("variant", "pv", 0, s_pv, HIDDEN);
		public final boolean useAuxiliaryQueues = addB("useAuxiliaryQueues", "uaq", false, s_uaq);
		public String classForRevisions = addS("classForRevisions", "cr", Reviser3.class, Reviser.class, s_rm);

		public boolean residues = addB("residues", "res", true, r1);
		public boolean bitResidues = addB("bitResidues", "bres", true, r2);
		public final boolean multidirectionality = addB("multidirectionality", "mul", true, "");
		public final int residueLimitForBitRm = addI("residueLimitForBitRm", "rbit", 499, "");
		public final int memoryLimitForBitRm = addI("memoryLimitForBitRm", "mbit", 550000000, "");

		public final int futureLimitation = addI("futureLimitation", "fl", -1, q1);
		public final int spaceLimitation = addI("spaceLimitation", "sl", 20, q2);
		public final int arityLimitForGACGuaranteed = addI("arityLimitForGACGuaranteed", "aggac", 2, q3);
		public boolean strongOnlyAtPreprocessing = addB("strongOnlyAtPreprocessing", "sop", false, "");
		public final boolean strongOnlyWhenACEffective = addB("strongOnlyWhenACEffective", "soe", false, "");
		public final boolean strongOnlyWhenNotSingleton = addB("strongOnlyWhenNotSingleton", "sons", true, "");
		public final String classForSACSelector = addS("classForSACSelector", "csac", CellIterator.class, "");
		public final int weakCutoff = addI("weakCutoff", "wc", 15, "");
		public final String classForFailedValues = addS("classForFailedValues", "fvc", "", "", HIDDEN);
	}

	public final SettingPropagation settingPropagation = new SettingPropagation();

	public class SettingShaving extends SettingGroup {
		public int parameter = addI("parameter", "s_p", 1, "", HIDDEN);
		public final double eligibilityThreshod = addD("eligibilityThreshod", "s_et", 3.0, "", HIDDEN);
		public final int limitedPropagationSamplingSize = addI("limitedPropagationSamplingSize", "s_lpss", 100, "", HIDDEN);
		public final double ratio = addD("ratio", "s_r", 0.0, "");
		public final double alpha = addD("alpha", "s_a", 0.0, "");
	}

	public final SettingShaving settingShaving = new SettingShaving();

	public class SettingLNS extends SettingGroup {
		public final boolean enabled = addB("enabled", "lns_e", false, "LNS activated if true");
		public final String heuristic = addS("heuristic", "lns_h", Rand.class, "class to be used when freezing");
		public final int nFreeze = addI("nFreeze", "lns_n", 0, "number of variables to freeze when restarting.");
		public final int pFreeze = addI("pFreeze", "lns_p", 10, "percentage of variables to freeze when restarting.");

	}

	public final SettingLNS settingLNS = new SettingLNS();

	public class SettingLB extends SettingGroup {
		private String s_e = "If true, local branching search is activated.";
		private String s_n = "The name of the class used for local branching constraints.";
		private String s_bd = "The maximum distance when exploring the neighborhood.";
		private String s_mr = "The max number of restarts for local branching before switching to classical search.";

		public final boolean enabled = addB("enabled", "lb_e", false, s_e);
		public final String neighborhood = addS("neighborhood", "lb_n", LBAtMostDistanceSum.class, SettingLB.class, s_n);
		public final int baseDistance = addI("baseDistance", "lb_bd", 1, s_bd);
		public final int maxRestarts = addI("maxRestarts", "lb_mr", 10, s_mr);
	}

	public final SettingLB settingLB = new SettingLB();

	public class SettingSolving extends SettingGroup {
		String s_class = "The name of the class used to explore the search space.\n\tTypically, this is " + SolverBacktrack.class.getSimpleName();
		String s_prepro = "If true, a preprocessing stage must be performed.";
		String s_search = "If true, search must be performed.";
		String s_branching = "The branching scheme used for search."
				+ "\n\tPossible values are bin for binary branching, non for non-binary (or d-way) branching, and res for restricted binarybranching.";

		public String clazz = addS("clazz", "s_class", SolverBacktrack.class, s_class);
		public boolean enablePrepro = addB("enablePrepro", "prepro", true, s_prepro);
		public boolean enableSearch = addB("enableSearch", "search", true, s_search);
		public final EBranching branching = addE("branching", "branching", EBranching.BIN, s_branching);
	}

	public final SettingSolving settingSolving = new SettingSolving();

	public class SettingRestarts extends SettingGroup {
		String s_n = "The maximal number of runs (restarts) to be performed.\n\tA value strictly greater than 1 is relevant only if a cutoff value is given.";
		String s_c = "The number of the counter (number of backtracks, number of failed assignments, ...) before the solver restarts."
				+ "\n\tWhen no value is given, the cutoff is set to Integer.MAX_VALUE.";
		String s_f = "The geometric increasing factor of the number (e.g. the number of failed assignments) used to break successive runs.";
		String s_m = "The kind of events to be counted so as to force restarts when the cutoff is reached.";
		String s_rrp = "Period, in term of number of restarts, for resetting restart data.";
		String s_rrc = "Coefficient used for increasing the cutoff, when restart data are reset";
		String s_rp = "";

		public int nRunsLimit = addI("nRunsLimit", "r_n", Integer.MAX_VALUE, s_n);
		public long cutoff = addL("cutoff", "r_c", 10, s_c); // for COP, this value is initially multiplied by 10 in Restarter
		public double factor = addD("factor", "r_f", 1.1, s_f);
		public final ERestartsMeasure measure = addE("measure", "r_m", ERestartsMeasure.FAILED, s_m);
		public int nRestartsResetPeriod = addI("nRestartsResetPeriod", "r_rrp", Integer.MAX_VALUE, s_rrp);
		public final int nRestartsResetCoefficient = addI("nRestartsResetCoefficient", "r_rrc", 2, s_rrc);
		public final int dataResetPeriod = addI("dataResetPeriod", "rp", Integer.MAX_VALUE, s_rp);
		public boolean restartAfterSolution = addB("restartAfterSolution", "ras", false, "");
		public boolean luby = addB("luby", "r_luby", false, "");
	}

	public final SettingRestarts settingRestarts = new SettingRestarts();

	public class SettingLearning extends SettingGroup {
		String s_ng = "Indicates the way nogoods are collected." + "\nBy default, this is nogood recording from restarts.";
		String s_bgbl = "The limit, in term of number of nogoods, for the base.";
		String s_ps = "Indicates the way partial states are collected." + "\nBy default, no such learning.";
		String s_pso = "Indicates which operators are used to extract partial states: a sequence of 5 bits is used.";

		public ELearningNogood nogood = addE("nogood", "l_ng", ELearningNogood.RST, s_ng);
		public final int nogoodBaseLimit = addI("nogoodBaseLimit", "l_ngbl", 200000, s_bgbl);
		public final int nogoodArityLimit = addI("nogoodArityLimit", "l_ngal", Integer.MAX_VALUE, "", HIDDEN);
		public final int unarySymmetryLimit = addI("unarySymmetryLimit", "l_usl", Integer.MAX_VALUE, "", HIDDEN);
		public final int nonunarySymmetryLimit = addI("nonunarySymmetryLimit", "l_nsl", 2000, "", HIDDEN);
		// public final boolean incrementNogoodWeight = addB("incrementNogoodWeight", "l_inw", false, "", HIDDEN);
		public final ELearningState state = addE("state", "l_ps", ELearningState.NO, s_ps);
		public final String stateOperators = addS("stateOperators", "l_pso", "11011", s_pso).trim();
		public final int compressionLevelForStateEquivalence = addI("compressionLevelForStateEquivalence", "l_clevel", Deflater.NO_COMPRESSION, "", HIDDEN);
		// BEST_SPEED or BEST_COMPRESSION as alternatives
		public final int compressionLimitForStateEquivalence = addI("compressionLimitForStateEquivalence", "l_climit", 300, "", HIDDEN);
	}

	public final SettingLearning settingLearning = new SettingLearning();

	public class SettingExtraction extends SettingGroup {
		String s_m = "The way the unsatisfiable cores will be identified." + "\n\tValid only with the command: java " + HeadExtraction.class.getName();
		String s_nc = "The number of cores (MUCs) that must be found." + "\n\tValid only with the command: java " + HeadExtraction.class.getName();
		String s_sc = "Indicates if cores must be saved in XCSP";

		public final EExtractionMethod method = addE("method", "e_m", EExtractionMethod.VAR, s_m);
		public final int nCores = addI("nCores", "e_nc", 1, s_nc);
		public final boolean saveCores = addB("saveCores", "e_sc", false, s_sc);
	}

	public final SettingExtraction settingExtraction = new SettingExtraction();

	public class SettingVarh extends SettingGroup {
		String s1 = "The name of the class that selects the variables to be assigned."
				+ "\n\tFor example, Dom indicates that at each step the next variable to be instantiated is the one with the smallest domain."
				+ "\n\tAnother example is varh=WDegOnDom that indicates that at each step the next variable to be instantiated is the one with the greatest ratio wdeg/dom,"
				+ "\n\t(which is equivalent to min dom/wdeg).";

		String s2 = "Indicates if we must follow the anti-heuristic.";
		String s3 = "With a value greater than or equal to 1, indicates that a reasoning from last conflicts must be used.";
		String s4 = "";
		String s5 = "";
		String s6 = "";

		public String classForVarHeuristic = addS("classForVarHeuristic", "varh", WdegVariant.Wdeg.class, HeuristicVariables.class, s1);
		public final boolean anti = addB("anti", "anti_varh", false, s2);
		public int lastConflictSize = addI("lastConflictSize", "lc", 2, s3);
		public final int initialWdeg = addI("initialWdeg", "iwd", 1, s4);
		public final EWeighting weighting = addE("weighting", "wt", EWeighting.CACD, s5);
		public final ESingletonAssignment singletonAssignment = addE("singletonAssignment", "sing", ESingletonAssignment.LAST, s6);
	}

	public final SettingVarh settingVarh = new SettingVarh();

	public class SettingValh extends SettingGroup {
		String s1 = "The name of the class that selects the next value to be assigned to the last selected variable."
				+ "\n\tAn example is valh=First that indicates that at each step the next value to be assigned is the first value in the current domain (a kind of lexicographic order).";
		String s2 = "Indicates if we must follow the anti-heuristic.";

		public String classForValHeuristic = addS("classForValHeuristic", "valh", heuristics.HeuristicValuesDirect.First.class, HeuristicValues.class, s1);
		public final boolean anti = addB("anti", "anti_valh", false, s2);

		public boolean runProgressSaving = addB("runProgressSaving", "rps", false, "");
		// bestSolution breaks determinism of search trees because it depends in which order domains are pruned (and becomes singleton or not)
		public boolean solutionSaving = addB("solutionSaving", "ss", true, "");
		public final int solutionSavingGap = addI("solutionSavingGap", "ssg", Integer.MAX_VALUE, "");
		public String warmStart = addS("warmStart", "warm", "", "").trim();

		public final boolean optValHeuristic = addB("optValHeuristic", "ovh", false, "");
	}

	public final SettingValh settingValh = new SettingValh();

	public class SettingRevh extends SettingGroup {
		String s1 = "The name of the class that represents the revision ordering heuristic.";
		String s2 = "Indicates if we must follow the anti-heuristic.";

		public final String classForRevHeuristic = addS("classForRevHeuristic", "revh", Dom.class, HeuristicRevisions.class, s1);
		public final boolean anti = addB("anti", "anti_revh", false, s2);
	}

	public final SettingRevh settingRevh = new SettingRevh();

	public class SettingLocalSearch extends SettingGroup {
		public final String classForNeighborHeuristic = addS("classForNeighborHeuristic", "cnh", BestGlobal.class, "");
		public final String classForTabu = addS("classForTabu", "cft", TabuManagerVariableValue.class, "");
		public final int tabuListSize = addI("tabuListSize", "tabs", 5, "");
		public final double thresholdForRandomVariableSelection = addD("thresholdForRandomVariableSelection", "trvars", 0.0, "");
		public final double thresholdForRandomValueSelection = addD("thresholdForRandomValueSelection", "trvals", 0.0, "");
	}

	public final SettingLocalSearch settingLocalSearch = new SettingLocalSearch();

	public class SettingExperimental extends SettingGroup {
		public final boolean testB = addB("testB", "test", false, "", HIDDEN);
		public int testI1 = addI("testI1", "testI1", 0, "", HIDDEN);
		public int testI2 = addI("testI2", "testI2", 0, "", HIDDEN);
		public int testI3 = addI("testI3", "testI3", 0, "", HIDDEN);
		public final boolean helene = addB("helene", "helene", false, "", HIDDEN);
		public final boolean save4Baudouin = addB("save4Baudouin", "s4b", false, "for synthetizing smart tables", HIDDEN);
	}

	public final SettingExperimental settingExperimental = new SettingExperimental();

	public class SettingHardCoding extends SettingGroup {
		public final boolean localSearchAtPreprocessing = false;
		public final int limitOfNbValuesForStrongConsistency = 50000;
		public boolean splitMDDConstraints = false;
		public final boolean weightingIncrementInConflictManager = true;
		public final String classForDecompositionSolver = "Decomposer2";
		public final long relationContractionLimit = 100000000;
		public boolean convertBooleanSumAsCountingCtr = false;
	}

	public final SettingHardCoding settingHardCoding = new SettingHardCoding();

	public final boolean mustBuildConflictStructures = settings.addB(3, "constraints", "mustBuildConflictStructures", "mbcs",
			!settingPropagation.classForRevisions.equals(Reviser.class.getSimpleName())
					|| (!settingValh.classForValHeuristic.equals(First.class.getSimpleName())
							&& !settingValh.classForValHeuristic.equals(Last.class.getSimpleName())),
			"");

	private Control() {
		int verbose = settingGeneral.verbose;
		Kit.control(verbose >= 0 && verbose <= 3, () -> "Verbose must be in 0..3");
		Kit.log.setLevel(verbose == 0 ? Level.CONFIG : verbose == 1 ? Level.FINE : verbose == 2 ? Level.FINER : Level.FINEST);
		if (settingGeneral.conditionForSatisfaction.trim().length() != 0) {
			String s = settingGeneral.conditionForSatisfaction;
			Kit.control(s.matches("\\((lt|le|ge|gt|ne|eq),\\d+\\)"), () -> "Bad form of the condition for satisfaction : " + s);
		}
		// () -> "The value of operatorForSatisfaction must be in {eq,ne,lt,le,gt,ge}.");
		Kit.control(0 <= settingLNS.pFreeze && settingLNS.pFreeze < 100, () -> "percentageOfVariablesToFreeze should be between 0 and 100 (excluded)");

		Kit.control(settingLearning.nogood != ELearningNogood.RST_SYM);
		Kit.control(settingOptimization.lowerBound <= settingOptimization.upperBound);
		// as
		// C0
		Kit.control(!settingCtrs.normalizeCtrs || (!settingProblem.isSymmetryBreaking() && settingGeneral.framework != TypeFramework.MAXCSP));
		settings.controlKeys();
		if (settingGeneral.makeExceptionsVisible)
			org.xcsp.modeler.Compiler.ev = true;
	}

	/**********************************************************************************************
	 ***** Class ControlPanelSettings
	 *********************************************************************************************/

	public static final class ControlPanelSettings {

		private UserSettings userSettings;

		private List<Setting<?>> settings = new ArrayList<>();

		public ControlPanelSettings(String settingsFilename) {
			this.userSettings = new UserSettings(settingsFilename);
		}

		/**********************************************************************************************
		 ***** Handling control panel settings (from the command line, and also possibly from a file)
		 *********************************************************************************************/

		private static class UserSettings {

			private Document document;

			private XPath xPath;

			private UserSettings(String userSettingsFilename) {
				if (userSettingsFilename == null)
					userSettingsFilename = Arguments.userSettingsFilename;
				if (userSettingsFilename != null && !userSettingsFilename.equals(Control.DEFAULT_CONFIGURATION)) {
					// Loads the XML file containing all settings from the user.
					document = DocumentHandler.load(new File(userSettingsFilename));
					xPath = XPathFactory.newInstance().newXPath();
				}
			}

			/** Returns the value (a String) of the specified attribute for the specified tag. */
			private String stringFor(String shortcut, String tag, String att, Object defaultValue) {
				// try with shortcut
				String value = shortcut == null ? null : Arguments.argsForCp.get(shortcut);
				if (value != null)
					return value.length() == 0 && !(defaultValue instanceof String) ? defaultValue.toString() : value;
				// try with tag+attribute
				value = Arguments.argsForCp.get((tag != null ? tag + "/" : "") + att);
				if (value != null)
					return value;
				if (document == null)
					return defaultValue.toString();
				// try in document
				try {
					NodeList nodes = (NodeList) xPath.compile("//" + (tag != null ? tag : "*") + "/@" + att).evaluate(document, XPathConstants.NODESET);
					Kit.control(nodes.getLength() <= 1, () -> "Problem with several possibilities for " + tag + " " + att);
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
				if (s.equals(Control.MIN))
					return longValue ? Long.MIN_VALUE : (Number) Integer.MIN_VALUE; // problem if cast omitted
				if (s.equals(Control.MAX) || s.equals(Control.ALL))
					return longValue ? Long.MAX_VALUE : (Number) Integer.MAX_VALUE; // problem if cast omitted
				char lastCharacter = s.charAt(s.length() - 1);
				Long baseValue = Kit.parseLong(Character.isDigit(lastCharacter) ? s : s.substring(0, s.length() - 1));
				Kit.control(baseValue != null, () -> "An integer/long value was expected for " + tag + "/" + att);
				double value = Character.isDigit(lastCharacter) ? baseValue
						: lastCharacter == 'k' || lastCharacter == 's' ? baseValue * 1000
								: lastCharacter == 'm' ? baseValue * 1000000 : (Double) Kit.exit("Bad character for " + tag + " " + att);
				Kit.control((longValue && Long.MIN_VALUE <= value && value <= Long.MAX_VALUE)
						|| (!longValue && Integer.MIN_VALUE <= value && value <= Integer.MAX_VALUE));
				return longValue ? new Long((long) value) : (Number) new Integer((int) value); // problem if cast omitted
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
				Utilities.control(d != null, "A double value was expected for " + tag + "/" + att);
				return d;
			}

			/** Returns the value (a boolean) of the specified attribute for the specified tag. */
			private boolean booleanFor(String shortcut, String tag, String att, Boolean defaultValue) {
				Boolean b = Utilities.toBoolean(stringFor(shortcut, tag, att, defaultValue));
				Utilities.control(b != null, "A boolean value was expected for " + tag + "/" + att);
				return b;
			}
		}

		private <T> Setting<T> add(Setting<T> setting) {
			Kit.control(setting.shortcut != null, () -> "A shortcut must be given");
			for (Setting<?> p : settings) {
				Kit.control(p.shortcut == null || !p.shortcut.equals(setting.shortcut),
						() -> "The parameters " + p.key() + " and " + setting.key() + " with the same shortcut " + setting.shortcut);
				Kit.control(!p.key().equals(setting.key()), () -> "The parameters " + p.key() + " and " + setting.key() + " with the same value");
			}
			settings.add(setting);
			Kit.control(setting.priority >= 1 && setting.priority <= 4 && setting.tag != null && setting.attribute != null && setting.defaultValue != null
					&& setting.value != null);
			return setting;
		}

		public int addI(int priority, String tag, String attribute, String shortcut, int defaultValue, String description) {
			return add(new Setting<Integer>(priority, tag, attribute, shortcut, defaultValue, description)).value;
		}

		public long addL(int priority, String tag, String attribute, String shortcut, long defaultValue, String description) {
			return add(new Setting<Long>(priority, tag, attribute, shortcut, defaultValue, description)).value;
		}

		public double addD(int priority, String tag, String attribute, String shortcut, double defaultValue, String description) {
			return add(new Setting<Double>(priority, tag, attribute, shortcut, defaultValue, description)).value;
		}

		public boolean addB(int priority, String tag, String attribute, String shortcut, boolean defaultValue, String description) {
			return add(new Setting<Boolean>(priority, tag, attribute, shortcut, defaultValue, description)).value;
		}

		public String addS(int priority, String tag, String attribute, String shortcut, String defaultValue, String description) {
			return add(new Setting<String>(priority, tag, attribute, shortcut, defaultValue, description)).value;
		}

		public String addS(int priority, String tag, String attribute, String shortcut, Class<?> defaultValue, Class<?> root, String description) {
			return add(new Setting<String>(priority, tag, attribute, shortcut, defaultValue, root, description)).value;
		}

		public <T extends Enum<T>> T addE(int priority, String tag, String attribute, String shortcut, T defaultValue, String description) {
			return add(new SettingEnum<T>(priority, tag, attribute, shortcut, defaultValue, description)).value;
		}

		public void controlKeys() {
			String k = Arguments.argsForCp.keySet().stream().filter(key -> settings.stream().noneMatch(s -> s.key().equals(key) || s.shortcut.equals(key)))
					.findFirst().orElse(null);
			Kit.control(k == null, () -> "The parameter " + k + " is unknown");
		}

		public void display() {
			try (Scanner scanner1 = new Scanner(Head.class.getResource("/displayPart1.txt").openStream());
					Scanner scanner2 = new Scanner(Head.class.getResourceAsStream("/displayPart2.txt"));) {
				while (scanner1.hasNext())
					System.out.println(scanner1.nextLine());
				String tag = null;
				for (Setting<?> setting : settings)
					if (setting.priority != Control.SettingGroup.HIDDEN && setting.priority != Control.SettingGroup.TO_IMPLEMENT)
						System.out.print((!setting.tag.equals(tag) ? "\n  " + (tag = setting.tag) + "\n" : "") + setting);
				System.out.println();
				while (scanner2.hasNext())
					System.out.println(scanner2.nextLine());
			} catch (Exception e) {
				Kit.exit("Error while loading display files", e);
			}
		}

		/**********************************************************************************************
		 ***** Class for storing all information concerning a setting
		 *********************************************************************************************/

		private class Setting<T> {

			private int priority;

			private String tag, attribute, shortcut, description;

			T defaultValue, value;

			private Class<?> root;

			private T getValue(String shortcut, String tag, String attribute, T defaultValue) {
				if (defaultValue == null)
					return null;
				Class<T> clazz = (Class<T>) defaultValue.getClass();
				if (defaultValue instanceof Integer)
					return clazz.cast(userSettings.intFor(shortcut, tag, attribute, (Integer) defaultValue));
				else if (defaultValue instanceof Long)
					return clazz.cast(userSettings.longFor(shortcut, tag, attribute, (Long) defaultValue));
				else if (defaultValue instanceof Double)
					return clazz.cast(userSettings.doubleFor(shortcut, tag, attribute, (Double) defaultValue));
				else if (defaultValue instanceof Boolean)
					return clazz.cast(userSettings.booleanFor(shortcut, tag, attribute, (Boolean) defaultValue));
				else if (defaultValue instanceof String)
					return clazz.cast(userSettings.stringFor(shortcut, tag, attribute, defaultValue));
				else if (defaultValue instanceof Enum<?>) {
					// Class<? extends Enum<?>> cl = (Class<? extends Enum<?>>) defaultValue.getClass();
					// Class<T> c = (Class<T>) defaultValue.getClass();
					// String s=""; return Enum.valueOf(cl, s.toUpperCase());
				}
				return null;
			}

			private Setting(int priority, String tag, String attribute, String shortcut, T defaultValue, String description) {
				this.priority = priority;
				this.tag = tag;
				this.attribute = attribute;
				this.shortcut = shortcut;
				this.defaultValue = defaultValue;
				this.value = getValue(shortcut, tag, attribute, defaultValue);
				this.description = description;
			}

			private Setting(int priority, String tag, String attribute, String shortcut, Class<?> defaultValue, Class<?> root, String description) {
				this(priority, tag, attribute, shortcut,
						(T) (defaultValue == null ? "" : defaultValue.getName().substring(defaultValue.getName().lastIndexOf(".") + 1)), description);
				this.root = root;
			}

			String key() {
				return tag + "/" + attribute; // (attributeAmbiguity ? tag + "/" : "") + attribute;
			}

			private final String[] experimentalNames = Kit.sort(new String[] { EExtension.STRCPRS.name(), EExtractionMethod.MAX_CSP.name(),
					EExtractionMethod.INC.name(), EExtractionMethod.INC_FIRST.name() });

			@Override
			public String toString() {
				String s = new String();
				s += "    -" + key() + (shortcut != null ? " -" + shortcut : "") + "\n";
				s += "\t" + (description == null || description.length() == 0 ? "Description is missing..." : description) + "\n";
				s += "\tDefault value is : " + (defaultValue instanceof String && ((String) defaultValue).length() == 0 ? "\"\" (empty string)" : defaultValue)
						+ "\n";
				if (root != null) {
					s += "\tPossible String values are : ";
					for (Class<?> cla : Reflector.searchClassesInheritingFrom(root))
						if (!(TagExperimental.class.isAssignableFrom(cla)) && !(TagInvisible.class.isAssignableFrom(cla)))
							s += cla.getSimpleName() + " ";
					s += "\n";
				}
				if (value instanceof Enum<?>) {
					s += "\tPossible Enum values are : ";
					for (Field field : value.getClass().getDeclaredFields())
						if (field.isEnumConstant() && Arrays.binarySearch(experimentalNames, field.getName()) < 0)
							// Kit.searchFirstStringOccurrenceIn(field.getName(), experimentalNames) == -1)
							s += field.getName() + " ";
					s += "\n";
				}
				return s;
			}
		}

		public final class SettingEnum<T extends Enum<T>> extends Setting<T> {
			private SettingEnum(int priority, String tag, String attribute, String shortcut, T defaultValue, String description) {
				super(priority, tag, attribute, shortcut, defaultValue, description);
				value = Enum.valueOf((Class<T>) defaultValue.getClass(), userSettings.stringFor(shortcut, tag, attribute, defaultValue).toUpperCase());
			}
		}

		public static void saveControlPanelSettings(Control cp, String outputFilename, int maximumPriority) {
			Document document = DocumentHandler.createNewDocument();
			Node root = document.appendChild(document.createElement(Control.CONFIGURATION));
			for (Setting<?> setting : cp.settings.settings)
				if (setting.priority <= maximumPriority) {
					NodeList list = document.getElementsByTagName(setting.tag);
					if (list.getLength() == 0) {
						root.appendChild(document.createElement(setting.tag));
						list = document.getElementsByTagName(setting.tag);
					}
					Kit.control(list.getLength() == 1);
					Object value = setting.defaultValue;
					if (value instanceof Number) {
						Number n = (Number) setting.defaultValue;
						value = n.longValue() == Long.MIN_VALUE || n.intValue() == Integer.MIN_VALUE ? "min"
								: n.longValue() == Long.MAX_VALUE || n.intValue() == Integer.MAX_VALUE ? "max" : value;
					}
					((Element) list.item(0)).setAttribute(setting.attribute.trim(), value.toString());
				}
			Utilities.save(document, outputFilename);
			try {
				Runtime.getRuntime().exec("xmlindent -i 2 -w " + outputFilename).waitFor();
			} catch (Exception e) {
				Utilities.exit("Pb when Indenting File " + outputFilename + " " + e);
			}
		}

	}

	/**********************************************************************************************
	 * Static section
	 *********************************************************************************************/

	public static final String DEFAULT_CONFIGURATION = "defaultConfiguration";
	public static final String CONFIGURATION = "configuration";

	public static final String MIN = "min";
	public static final String MAX = "max";
	public static final String ALL = "all";

	private static String staticUserSettingsFilename;

	public static synchronized Control buildControlPanelFor(String userSettingsFilename) {
		Control.staticUserSettingsFilename = userSettingsFilename;
		return new Control();
	}

	public static void main(String[] args) {
		Integer maximumPriority = args.length != 2 ? null : Kit.parseInteger(args[1]);
		if (args.length != 2 || maximumPriority == null || maximumPriority < 1 || maximumPriority > 3) {
			System.out.println("\tTool used to generate a default settings file.");
			System.out.println("\tUsage : " + Control.class.getName() + " <outputFileName> <maximumPriority>");
			System.out.println("\n\toutputFileName : name of the generated configuration file.");
			System.out.println(
					"\n\tmaximumPriority : the generated file contains only parameters with a priority value lower than this number (must be between 1 and 3)");
		} else {
			new File(Kit.getPathOf(args[0])).mkdirs();
			ControlPanelSettings.saveControlPanelSettings(buildControlPanelFor(null), args[0] + (args[0].endsWith(".xml") ? "" : ".xml"), maximumPriority);
		}
	}
}
