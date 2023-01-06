/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package problem;

import static java.util.stream.Collectors.groupingBy;
import static java.util.stream.Collectors.summingLong;
import static org.xcsp.common.Constants.PLUS_INFINITY_INT;
import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.NE;
import static org.xcsp.common.Types.TypeExpr.ADD;
import static org.xcsp.common.Types.TypeExpr.IFF;
import static org.xcsp.common.Types.TypeExpr.LONG;
import static org.xcsp.common.Types.TypeExpr.MUL;
import static org.xcsp.common.Types.TypeExpr.VAR;
import static org.xcsp.common.Types.TypeObjective.EXPRESSION;
import static org.xcsp.common.Types.TypeObjective.LEX;
import static org.xcsp.common.Types.TypeObjective.MAXIMUM;
import static org.xcsp.common.Types.TypeObjective.MINIMUM;
import static org.xcsp.common.Types.TypeObjective.NVALUES;
import static org.xcsp.common.Types.TypeObjective.SUM;
import static org.xcsp.common.Types.TypeOptimization.MAXIMIZE;
import static org.xcsp.common.Types.TypeOptimization.MINIMIZE;
import static org.xcsp.common.Utilities.safeInt;
import static org.xcsp.common.predicates.MatcherInterface.add_mul_vals;
import static org.xcsp.common.predicates.MatcherInterface.add_mul_vars;
import static org.xcsp.common.predicates.MatcherInterface.add_vars;
import static org.xcsp.common.predicates.MatcherInterface.logic_vars;
import static org.xcsp.common.predicates.MatcherInterface.max_vars;
import static org.xcsp.common.predicates.MatcherInterface.min_vars;
import static org.xcsp.common.predicates.MatcherInterface.mul_vars;
import static org.xcsp.common.predicates.MatcherInterface.set_vals;
import static org.xcsp.common.predicates.MatcherInterface.val;
import static org.xcsp.common.predicates.MatcherInterface.var;
import static org.xcsp.common.predicates.MatcherInterface.varOrVal;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.ariop;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.relop;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.setop;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.unalop;
import static org.xcsp.common.predicates.XNode.node;
import static org.xcsp.common.predicates.XNodeParent.add;
import static org.xcsp.common.predicates.XNodeParent.build;
import static org.xcsp.common.predicates.XNodeParent.eq;
import static org.xcsp.common.predicates.XNodeParent.ge;
import static org.xcsp.common.predicates.XNodeParent.iff;
import static org.xcsp.common.predicates.XNodeParent.in;
import static org.xcsp.common.predicates.XNodeParent.le;
import static org.xcsp.common.predicates.XNodeParent.mul;
import static org.xcsp.common.predicates.XNodeParent.or;
import static org.xcsp.common.predicates.XNodeParent.set;
import static utility.Kit.log;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.IntFunction;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Condition;
import org.xcsp.common.Condition.ConditionIntset;
import org.xcsp.common.Condition.ConditionIntvl;
import org.xcsp.common.Condition.ConditionRel;
import org.xcsp.common.Condition.ConditionSet;
import org.xcsp.common.Condition.ConditionVal;
import org.xcsp.common.Condition.ConditionVar;
import org.xcsp.common.Constants;
import org.xcsp.common.FunctionalInterfaces.IntToDom;
import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.IVar.VarSymbolic;
import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeClass;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeObjective;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeOptimization;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.Utilities;
import org.xcsp.common.Utilities.ModifiableBoolean;
import org.xcsp.common.domains.Domains.Dom;
import org.xcsp.common.domains.Domains.DomSymbolic;
import org.xcsp.common.domains.Values.IntegerEntity;
import org.xcsp.common.domains.Values.IntegerInterval;
import org.xcsp.common.predicates.MatcherInterface.Matcher;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.common.structures.AbstractTuple;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;
import org.xcsp.modeler.entities.CtrEntities.CtrArray;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;
import org.xcsp.modeler.entities.ObjEntities.ObjEntity;
import org.xcsp.modeler.entities.VarEntities.VarArray;
import org.xcsp.modeler.implementation.ProblemIMP;

import constraints.ConflictsStructure;
import constraints.Constraint;
import constraints.Constraint.CtrTrivial.CtrFalse;
import constraints.Constraint.CtrTrivial.CtrTrue;
import constraints.ConstraintExtension;
import constraints.ConstraintExtension.Extension1;
import constraints.ConstraintIntension;
import constraints.extension.CHybrid;
import constraints.extension.CMDD.CMDDO;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableHybrid.HybridTuple;
import constraints.global.AllDifferent.AllDifferentComplete;
import constraints.global.AllDifferent.AllDifferentCounting;
import constraints.global.AllDifferent.AllDifferentExceptWeak;
import constraints.global.AllDifferent.AllDifferentPermutation;
import constraints.global.AllDifferent.AllDifferentWeak;
import constraints.global.AllEqual;
import constraints.global.Among;
import constraints.global.BinPacking.BinPackingEnergetic;
import constraints.global.BinPacking.BinPackingEnergeticLoad;
import constraints.global.Cardinality;
import constraints.global.Circuit;
import constraints.global.Circuit2;
import constraints.global.Count.CountCst.AtLeast1;
import constraints.global.Count.CountCst.AtLeastK;
import constraints.global.Count.CountCst.AtMost1;
import constraints.global.Count.CountCst.AtMostK;
import constraints.global.Count.CountCst.Exactly1;
import constraints.global.Count.CountCst.ExactlyK;
import constraints.global.Count.CountVar.ExactlyVarK;
import constraints.global.Cumulative.CumulativeCst;
import constraints.global.Cumulative.CumulativeVarC;
import constraints.global.Cumulative.CumulativeVarH;
import constraints.global.Cumulative.CumulativeVarHC;
import constraints.global.Cumulative.CumulativeVarW;
import constraints.global.Cumulative.CumulativeVarWC;
import constraints.global.Cumulative.CumulativeVarWH;
import constraints.global.Cumulative.CumulativeVarWHC;
import constraints.global.DistinctLists;
import constraints.global.Element.ElementList.ElementCst;
import constraints.global.Element.ElementList.ElementVar;
import constraints.global.Element.ElementMatrix.ElementMatrixCst;
import constraints.global.Element.ElementMatrix.ElementMatrixVar;
import constraints.global.Extremum.ExtremumCst;
import constraints.global.Extremum.ExtremumCst.MaximumCst;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstGE;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.global.Extremum.ExtremumCst.MinimumCst;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstGE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstLE;
import constraints.global.Extremum.ExtremumVar.Maximum;
import constraints.global.Extremum.ExtremumVar.Minimum;
import constraints.global.ExtremumArg.ExtremumArgVar.MaximumArg;
import constraints.global.ExtremumArg.ExtremumArgVar.MinimumArg;
import constraints.global.Lexicographic;
import constraints.global.NValues.NValuesCst;
import constraints.global.NValues.NValuesCst.NValuesCstGE;
import constraints.global.NValues.NValuesCst.NValuesCstLE;
import constraints.global.NValues.NValuesVar;
import constraints.global.NoOverlap;
import constraints.global.Precedence;
import constraints.global.Product.ProductSimple;
import constraints.global.Sum.SumSimple;
import constraints.global.Sum.SumSimple.SumSimpleGE;
import constraints.global.Sum.SumSimple.SumSimpleLE;
import constraints.global.Sum.SumViewWeighted;
import constraints.global.Sum.SumWeighted;
import constraints.global.Sum.SumWeighted.SumWeightedEQ;
import constraints.global.Sum.SumWeighted.SumWeightedGE;
import constraints.global.Sum.SumWeighted.SumWeightedLE;
import constraints.global.SumScalarBoolean.SumScalarBooleanCst;
import constraints.global.SumScalarBoolean.SumScalarBooleanVar;
import constraints.intension.Primitive2;
import constraints.intension.Primitive2.PrimitiveBinaryNoCst.Disjonctive;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Sub2;
import constraints.intension.Primitive3;
import constraints.intension.Primitive3.Add3;
import constraints.intension.Primitive4.Disjonctive2D;
import constraints.intension.Primitive4.DisjonctiveVar;
import constraints.intension.Reification.Reif2;
import constraints.intension.Reification.Reif2.Reif2EQ;
import constraints.intension.Reification.Reif3;
import constraints.intension.Reification.ReifLogic;
import dashboard.Control.OptionsGeneral;
import dashboard.Control.OptionsGlobal;
import dashboard.Control.OptionsIntension;
import heuristics.HeuristicValues;
import interfaces.Observers.ObserverOnConstruction;
import main.Head;
import optimization.ObjectiveVariable;
import optimization.ObjectiveVariable.ObjVarGE;
import optimization.ObjectiveVariable.ObjVarLE;
import optimization.Optimizable;
import optimization.Optimizer;
import optimization.Optimizer.OptimizationStrategy;
import optimization.Optimizer.OptimizerDecreasing;
import optimization.Optimizer.OptimizerDichotomic;
import optimization.Optimizer.OptimizerIncreasing;
import problem.Reinforcer.Automorphisms;
import problem.Reinforcer.Cliques;
import solver.Solver;
import utility.Kit;
import utility.Kit.Color;
import utility.Stopwatch;
import variables.Domain;
import variables.DomainFinite.DomainRange;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

/**
 * This is the class for representing problems (constraint networks).
 * 
 * @author Christophe Lecoutre
 *
 */
public final class Problem extends ProblemIMP implements ObserverOnConstruction {

	public static final String AUXILIARY_VARIABLE_PREFIX = "_ax_";

	public static final int BASE = 0;
	public static final int INTENSION_DECOMPOSITION = 1;
	public static final int EXTENSION_ORDINARY = 2;
	public static final int EXTENSION_STARRED = 22;
	public static final int EXTENSION_HYBRID = 222;

	/**
	 * Different ways of breaking symmetries
	 */
	public static enum SymmetryBreaking {
		NO, SB_LE, SB_LEX;
	}

	/**********************************************************************************************
	 *** Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		assert Stream.of(variables).map(x -> x.id()).distinct().count() == n : "Two variables have the same id";
		assert Variable.areNumsNormalized(variables) : "Non normalized nums in the problem";
		assert Constraint.areNumsNormalized(constraints) : "Non normalized nums in the problem";

		this.framework = optimizer != null ? TypeFramework.COP : TypeFramework.CSP; // currently, MAXCSP is not possible
		head.control.framework(optimizer); // modifying a few options
		for (Variable x : variables) {
			assert Stream.of(x.ctrs).noneMatch(c -> c.num == -1);
			x.dom.setNumberOfLevels(n + 1);
		}
		this.priorityVars = priorityVars.length == 0 && annotations.decision != null ? (Variable[]) annotations.decision : priorityVars;
		Variable[] r = HeuristicValues.possibleOptimizationInterference(this);
		this.priorityVars = r != null ? r : priorityVars;
		this.arrays = varEntities.varArrays.stream().filter(va -> !va.id.startsWith(AUXILIARY_VARIABLE_PREFIX)).toArray(VarArray[]::new);
		control(priorityVars.length == 0 || !head.control.variables.stayArrayFocus);
		control(priorityVars.length == 0 || (head.control.variables.priorityArrays.length() == 0 && !head.control.varh.arrayPriorityRunRobin));
		int[] indexes = Stream.of(Kit.extractFrom(head.control.variables.priorityArrays))
				.mapToInt(
						v -> v instanceof Integer ? (Integer) v : IntStream.range(0, arrays.length).filter(i -> arrays[i].id.equals(v)).findFirst().orElse(-1))
				.toArray();
		control(IntStream.of(indexes).allMatch(i -> 0 <= i && i < arrays.length),
				"the value of the option -pra is not valid: " + head.control.variables.priorityArrays);
		this.priorityArrays = IntStream.of(indexes).mapToObj(i -> arrays[i]).toArray(VarArray[]::new);
	}

	@Override
	public void afterSolverConstruction() {
		ConflictsStructure.buildFor(this);
	}

	/**********************************************************************************************
	 *** Inner Class Symbolic
	 *********************************************************************************************/

	public static final class Symbolic {

		public final Map<String, Integer> mapOfSymbols = new HashMap<>();

		public int[] manageSymbols(String[] symbols) {
			int[] t = new int[symbols.length];
			for (int i = 0; i < t.length; i++) {
				assert !symbols[i].equals(Constants.STAR_SYMBOL);
				t[i] = mapOfSymbols.computeIfAbsent(symbols[i], k -> mapOfSymbols.size());
			}
			return t;
		}

		public String[] replaceSymbols(String[] tokens) {
			String[] t = new String[tokens.length];
			for (int i = 0; i < t.length; i++) {
				Integer v = mapOfSymbols.get(tokens[i]);
				t[i] = v != null ? v.toString() : tokens[i];
			}
			return t;
		}

		public int[][] replaceSymbols(String[][] tuples) {
			int[][] m = new int[tuples.length][];
			for (int i = 0; i < m.length; i++) {
				m[i] = new int[tuples[i].length];
				for (int j = 0; j < m[i].length; j++) {
					Integer v = mapOfSymbols.get(tuples[i][j]);
					m[i][j] = v != null ? v : tuples[i][j].equals(Constants.STAR_SYMBOL) ? Constants.STAR : Integer.parseInt(tuples[i][j]);
				}
			}
			return m;
		}
	}

	/**********************************************************************************************
	 *** Fields and General Methods
	 *********************************************************************************************/

	/**
	 * The main object, leading (head of) resolution
	 */
	public final Head head;

	/**
	 * The solver used to solve the problem; equivalent to head.solver.
	 */
	public Solver solver;

	/**
	 * The framework of the problem (CSP or COP); currently, MAXCSP is not managed
	 */
	public TypeFramework framework;

	/**
	 * The set of variables of the problem, in the order they have been defined (posted).
	 */
	public Variable[] variables;

	/**
	 * The set of constraints of the problem, in the order they have been defined (posted).
	 */
	public Constraint[] constraints;

	/**
	 * The pilot for handling the objective of the problem, if any (otherwise, null).
	 */
	public Optimizer optimizer;

	/**
	 * The priority variables. For example, those that have to be assigned in priority by a backtrack search solver.
	 * There is 0 priority variable by default.
	 */
	public Variable[] priorityVars = new Variable[0];

	/**
	 * The priority variables put in the array above at indices ranging from 0 to this field value should be assigned
	 * strictly in that order.
	 */
	public int nStrictPriorityVars;

	/**
	 * An object used to record many data corresponding to metrics and various features of the problem.
	 */
	public Features features;

	/**
	 * The object used to manage symbolic values. Basically, it transforms symbols into integers, but this is not
	 * visible for the user (modeler).
	 */
	public Symbolic symbolic = new Symbolic();

	/**
	 * The list of generators of an identified symmetry group of variables. Maybe, empty.
	 */
	public final List<List<int[]>> symmetryGroupGenerators = new ArrayList<>();

	/**
	 * The general options
	 */
	public final OptionsGeneral options;

	/**
	 * The accumulated number of removals (value deletions) made all along the solving process
	 */
	public int nValueRemovals;

	/**
	 * The number of auxiliary variables introduced when replacing tree expressions
	 */
	public int nAuxVariables;

	/**
	 * The variable arrays, as present in the XCSP3 instance (excluding the possibly introduced auxiliary arrays)
	 */
	public VarArray[] arrays;

	/**
	 * The priority variable arrays, subset of arrays (usually, empty)
	 */
	public VarArray[] priorityArrays;

	/**
	 * The number of auxiliary (equality) constraints introduced when replacing tree expressions
	 */
	public int nAuxConstraints;

	@Override
	public final String name() {
		String name = super.name();
		return name.matches("XCSP[23]-.*") ? name.substring(6) : name;
	}

	/**
	 * Method that resets the problem instance. Each variable and each constraint is reset. The specified Boolean
	 * parameter indicates whether the weighted degrees values must not be reset or not. Currently, this is only used by
	 * HeadExtraction.
	 */
	public void reset() {
		Stream.of(variables).forEach(x -> x.reset());
		Stream.of(constraints).forEach(c -> c.reset());
		Stream.of(constraints).forEach(c -> c.ignored = false);
		// should we rebuild a Features object?
		nValueRemovals = 0;
		if (options.verbose > 0)
			log.info("Reset of problem instance");
	}

	public void reduceTo(boolean[] presentVariables, boolean[] presentConstraints) {
		// currently, used by HeadExtraction
		control(symmetryGroupGenerators.size() == 0 && presentVariables.length == variables.length && presentConstraints.length == constraints.length);
		assert Variable.firstWipeoutVariableIn(variables) == null && Variable.areNumsNormalized(variables) && Constraint.areNumsNormalized(constraints);
		priorityVars = IntStream.range(0, variables.length).filter(i -> presentVariables[i]).mapToObj(i -> variables[i]).toArray(Variable[]::new);
		for (Variable x : priorityVars)
			x.reset();
		for (int i = 0; i < constraints.length; i++)
			if (!(constraints[i].ignored = !presentConstraints[i]))
				constraints[i].reset();
		// features = new Features(this); // TODO reset or building a new object?
		nValueRemovals = 0;
		if (options.verbose > 0)
			log.info("Reduction to (#V=" + priorityVars.length + ",#C=" + Kit.countIn(true, presentConstraints) + ")");
	}

	private void inferAdditionalConstraints() {
		Stopwatch stopwatch = new Stopwatch();
		List<Variable> variables = features.collecting.variables;
		List<Constraint> constraints = features.collecting.constraints;
		if (head.control.problem.symmetryBreaking != SymmetryBreaking.NO) {
			int nBefore = constraints.size();
			List<List<int[]>> generators = Automorphisms.buildGenerators(variables, constraints);
			for (List<int[]> generator : generators) {
				int[] cycle1 = generator.get(0);
				Variable x = variables.get(cycle1[0]);
				Variable y = variables.get(cycle1[1]);
				if (head.control.problem.symmetryBreaking == SymmetryBreaking.SB_LE)
					lessEqual(x, y); // we only consider the two first variables
				else {
					List<Variable> list1 = new ArrayList<>(), list2 = new ArrayList<>();
					for (int[] cycle : generator)
						if (cycle.length == 2) {
							list1.add(variables.get(cycle[0]));
							list2.add(variables.get(cycle[1]));
						} else
							for (int i = 0; i < cycle.length; i++) {
								list1.add(variables.get(cycle[i]));
								list2.add(variables.get(cycle[(i + 1) % cycle.length]));
							}
					VariableInteger[] t1 = list1.toArray(new VariableInteger[list1.size()]), t2 = list2.toArray(new VariableInteger[list2.size()]);
					control(IntStream.range(0, t1.length - 1).noneMatch(i -> t1[i].compareTo(t1[i + 1]) >= 0));
					lexSimple(t1, t2, TypeOperatorRel.LE);
				}
			}
			symmetryGroupGenerators.addAll(generators);
			features.nGenerators = generators.size();
			features.nAddedCtrs += constraints.size() - nBefore;
			if (head.control.general.verbose > 0)
				System.out.println("Time for generating symmetry-breaking constraints: " + stopwatch.wckTimeInSeconds());
		}
		OptionsGlobal options = head.control.global;
		if (options.allDifferentNb > 0) {
			stopwatch.start();
			List<Variable[]> cliques = Cliques.buildCliques(variables, constraints, options.allDifferentNb, options.allDifferentSize);
			for (Variable[] clique : cliques)
				allDifferent(clique);
			features.nCliques = cliques.size();
			if (head.control.general.verbose > 0)
				System.out.println("Time for generating redundant AllDifferent constraints: " + stopwatch.wckTimeInSeconds());
		}
	}

	/**
	 * This method is called when the initialization is finished in order to put, among other things, variables and
	 * constraints into arrays.
	 */
	private final void storeToArrays() {
		features.collecting.fix();
		this.variables = features.collecting.variables.toArray(new Variable[0]);
		this.constraints = features.collecting.constraints.toArray(new Constraint[0]);

		Constraint[] sortedConstraints = features.collecting.constraints.stream().sorted((c1, c2) -> c1.scp.length - c2.scp.length).toArray(Constraint[]::new);
		// TODO for the moment we cannot use the sortedConstraints as the main array (pb with nums, and anyway would it
		// be useful?)
		List<Constraint>[] lists = IntStream.range(0, variables.length).mapToObj(i -> new ArrayList<>()).toArray(List[]::new);
		for (Constraint c : sortedConstraints)
			for (Variable x : c.scp)
				lists[x.num].add(c);
		for (Variable x : variables)
			x.storeInvolvingConstraints(lists[x.num]);
		assert Variable.areNumsNormalized(variables);// && Constraint.areIdsNormalized(constraints); TODO
	}

	/**
	 * @param o
	 *            an object that must be either the id of a variable or the number of a variable
	 * @return the variable with the specified id or number
	 */
	public Variable variableWithNumOrId(Object o) {
		Variable x = o instanceof Integer ? variables[(Integer) o] : mapForVars.get(o);
		assert x != null : "The variable " + o + " cannot be found";
		assert x.num != Variable.UNSET_NUM : "You cannot use the discarded variable " + o;
		return x;
	}

	/**
	 * Takes into account the instantiation possibly specified by the user, by reducing domains
	 */
	private void reduceDomainsFromUserInstantiationAndRefutation() {
		String instantiation = head.control.variables.instantiation;
		if (instantiation.length() > 0) {
			String[] t = instantiation.split(":");
			control(t.length == 2, "Problem with " + instantiation);
			Object[] vars = Kit.extractFrom(t[0]);
			int[] vals = Utilities.toIntegers(t[1].split(","));
			control(vars.length == vals.length, "In the instantiation, the number of variables (ids or nums) is different from the number of values.");
			for (int i = 0; i < vars.length; i++) {
				Variable x = variableWithNumOrId(vars[i]);
				int v = vals[i];
				assert x.dom.containsValue(v) : "Value " + v + " not present in domain of " + x + ". Check  -ins.";
				x.dom.removeValuesAtConstructionTime(w -> w != v);
			}
		}
		String refutation = head.control.variables.refutation;
		if (refutation.length() > 0) {
			String[] t = refutation.split(":");
			control(t.length == 2, "Problem with " + refutation);
			Object[] vars = Kit.extractFrom(t[0]);
			int[] vals = Utilities.toIntegers(t[1].split(","));
			control(vars.length == vals.length, "In the refutation, the number of variables (ids or nums) is different from the number of values.");
			for (int i = 0; i < vars.length; i++) {
				Variable x = variableWithNumOrId(vars[i]);
				int v = vals[i];
				assert x.dom.containsValue(v) : "Value " + v + " not present in domain of " + x + ". Check  -ref.";
				x.dom.removeValueAtConstructionTime(v);
			}
		}
	}

	/**
	 * If the context allows it, reduce the domains of isolated variables (i.e., involved in no constraint) to an
	 * arbitrary value
	 */
	private void reduceDomainsOfIsolatedVariables() {
		// TODO other frameworks ?
		boolean reduceIsolatedVars = head.control.variables.reduceIsolated && framework == TypeFramework.CSP && options.solLimit == 1
				&& head.control.problem.symmetryBreaking == SymmetryBreaking.NO;
		List<Variable> isolatedVars = new ArrayList<>(), fixedVars = new ArrayList<>();
		int nRemovedValues = 0;
		for (Variable x : variables) {
			if (x.ctrs.length == 0) {
				isolatedVars.add(x);
				if (reduceIsolatedVars) {
					nRemovedValues += x.dom.size() - 1;
					x.dom.removeValuesAtConstructionTime(v -> v != x.dom.firstValue()); // first value arbitrarily kept
				}
			}
			if (x.dom.size() == 1)
				fixedVars.add(x);
		}
		if (isolatedVars.size() > 0) {
			features.nIsolatedVars += isolatedVars.size();
			log.info("Isolated variables : " + Kit.join(isolatedVars));
			log.info("Nb values removed due to isolated variables : " + nRemovedValues + "\n");
		}
		if (fixedVars.size() > 0) {
			features.nFixedVars += fixedVars.size();
			log.info("Fixed variables : " + (fixedVars.size() <= 100 ? Kit.join(fixedVars) : "more than 100") + "\n");
		}
	}

	public Variable replacedObjVar;

	private void replaceObjectiveVariable() {
		if (head.control.optimization.replaceObjVar && optimizer != null && optimizer.ctr instanceof ObjectiveVariable) {
			Variable x = ((ObjectiveVariable) optimizer.ctr).x;
			Constraint[] t = features.collecting.constraints.stream().filter(c -> c.involves(x)).toArray(Constraint[]::new);
			if (x.dom instanceof DomainRange && t.length == 3 && t[1] == optimizer.clb && t[2] == optimizer.cub) {
				if (t[0] instanceof SumWeightedEQ) {
					Variable[] scp = t[0].scp;
					int[] coeffs = ((SumWeighted) t[0]).coeffs;
					int pos = Utilities.indexOf(x, t[0].scp);
					control(pos != -1, " " + Kit.join(t[0].scp) + " - " + x + " " + pos);
					if (coeffs[pos] == -1)
						return; // How to handle that? (anyway, it must be rare (see StillLife-wastage-03.xml)
					if (coeffs[pos] != 1)
						return;
					TypeOptimization opt = optimizer.minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE;
					for (Constraint c : t) {
						// c.ignored = true;
						head.observersConstruction.remove(c);
						features.collecting.constraints.remove(c);
					}
					features.collecting.variables.remove(x);
					// x.dom = new DomainRange(x, 0, 0);
					optimizer = null;
					optimize(opt, TypeObjective.SUM, IntStream.range(0, scp.length).filter(i -> i != pos).mapToObj(i -> scp[i]).toArray(Variable[]::new),
							IntStream.range(0, coeffs.length).filter(i -> i != pos).map(i -> coeffs[i]).toArray());
					if (x.dom.firstValue() > optimizer.clb.limit()) {
						optimizer.clb.setLimit(x.dom.firstValue());
						optimizer.minBound = x.dom.firstValue();
					}
					if (x.dom.lastValue() < optimizer.cub.limit()) {
						optimizer.cub.setLimit(x.dom.lastValue());
						optimizer.maxBound = x.dom.lastValue();
					}
					replacedObjVar = x;
				}
			}
		}
	}

	public Problem(ProblemAPI api, String modelVariant, String data, String dataFormat, boolean dataSaving, String[] argsForPb, Head head) {
		super(api, modelVariant, argsForPb);
		this.head = head;
		head.problem = this; // required because it is needed during the initialization of some objects
		head.observersConstruction.add(0, this); // Must be the first in the list when calling afterSolverConstruction
		this.options = head.control.general;
		this.features = new Features(this);

		// we load data and build the model (we follow the scheme of the Compiler API from XCSP-Java-Tools)
		head.output.beforeData();
		loadData(data, dataFormat, dataSaving);
		head.output.afterData();
		api.model();

		replaceObjectiveVariable();

		// after possibly adding some additional constraints, we store variables and constraints into arrays
		inferAdditionalConstraints();
		storeToArrays();

		// we may reduce the domains of some variables
		reduceDomainsFromUserInstantiationAndRefutation();
		reduceDomainsOfIsolatedVariables();
	}

	/**
	 * Displays information about the (variables and constraints of the) problem
	 */
	public final void display() {
		if (options.verbose >= 2) {
			log.finer("\nProblem " + name());
			Stream.of(variables).forEach(x -> x.display(options.verbose == 3));
			Stream.of(constraints).forEach(c -> c.display(options.verbose == 3));
		}
	}

	/**********************************************************************************************
	 *** Posting Variables
	 *********************************************************************************************/

	/**
	 * A map that gives access to each variable through its id.
	 */
	private final Map<String, Variable> mapForVars = new HashMap<>();

	/**
	 * A cache used to avoid computing several times the same sets of values
	 */
	private final Map<Object, int[]> cache = new HashMap<>();

	/**
	 * Posts the specified variable, i.e., records it as being a variable of the problem
	 * 
	 * @param x
	 *            a variable to be posted
	 * @return the posted variable
	 */
	private final Variable post(Variable x) {
		control(!mapForVars.containsKey(x.id()), x.id() + " duplicated");
		int num = features.collecting.add(x);
		if (num == -1)
			return null; // because the variable is discarded
		x.num = num;
		mapForVars.put(x.id(), x);
		return x;
	}

	@Override
	public Class<VariableInteger> classVI() {
		return VariableInteger.class;
	}

	@Override
	public Class<VariableSymbolic> classVS() {
		return VariableSymbolic.class;
	}

	@Override
	public TypeFramework typeFramework() {
		return framework;
	}

	@Override
	public VariableInteger buildVarInteger(String id, Dom dom) {
		VariableInteger x = null;
		if (dom.values.length == 1 && dom.values[0] instanceof IntegerInterval)
			x = new VariableInteger(this, id, (IntegerInterval) dom.values[0]);
		else
			x = new VariableInteger(this, id, cache.computeIfAbsent(dom.values, k -> IntegerEntity.toIntArray((IntegerEntity[]) k)));
		return (VariableInteger) post(x);
	}

	@Override
	public VariableSymbolic buildVarSymbolic(String id, DomSymbolic dom) {
		return (VariableSymbolic) post(new VariableSymbolic(this, id, (String[]) dom.values));
	}

	// ************************************************************************
	// ***** Replacing trees by variables and simplifying conditions
	// ************************************************************************

	private XNode<IVar>[] treesToArray(Stream<XNode<IVar>> trees) {
		return trees.toArray(XNode[]::new);
	}

	private String idAux() {
		return AUXILIARY_VARIABLE_PREFIX + varEntities.allEntities.size();
	}

	private Var auxVar(Object values) {
		nAuxVariables++;
		return api.var(idAux(), values instanceof Range ? api.dom((Range) values) : api.dom((int[]) values), "auxiliary variable");
	}

	private Var[] auxVarArray(int length, Object values) {
		nAuxVariables += length;
		control(length > 1);
		values = values instanceof Range ? api.dom((Range) values) : values instanceof int[] ? api.dom((int[]) values) : values;
		if (values instanceof Dom)
			return api.array(idAux(), api.size(length), (Dom) values, "auxiliary variables");
		return api.array(idAux(), api.size(length), (IntToDom) values, "auxiliary variables");
	}

	private void replacement(Var aux, XNode<IVar> tree, boolean tuplesComputed, int[][] tuples) {
		nAuxConstraints++;
		Variable[] treeVars = (Variable[]) tree.vars();
		if (!tuplesComputed && head.control.intension.toExtension(treeVars, null))
			tuples = new TreeEvaluator(tree).computeTuples(Variable.initDomainValues(treeVars), null); // or current
																										// values?
		if (tuples != null) {
			features.nConvertedConstraints++;
			extension(vars(treeVars, aux), tuples, true);
		} else
			equal(aux, tree);
	}

	/**
	 * Returns a new (auxiliary) variable representing the specified tree expression after having posted an equality
	 * constraint, i.e., a constraint forcing the new variable to be equal to the tree expression
	 * 
	 * @param tree
	 *            a tree expression
	 * @return a new (auxiliary) variable representing the specified tree expression
	 */
	public Variable replaceByVariable(XNode<IVar> tree) {
		Var aux = auxVar(tree.possibleValues());
		replacement(aux, tree, false, null);
		return (Variable) aux;
	}

	private boolean areSimilar(XNode<IVar> tree1, XNode<IVar> tree2) {
		if (tree1.type != tree2.type || tree1.arity() != tree2.arity())
			return false;
		if (tree1.arity() == 0) {
			Object value1 = ((XNodeLeaf<?>) tree1).value, value2 = ((XNodeLeaf<?>) tree2).value;
			return tree1.type == TypeExpr.VAR ? ((Variable) value1).dom.typeIdentifier() == ((Variable) value2).dom.typeIdentifier() : value1.equals(value2);
		}
		return IntStream.range(0, tree1.arity()).allMatch(i -> areSimilar(tree1.sons[i], tree2.sons[i]));
	}

	/**
	 * Returns an array of new (auxiliary) variables representing the specified tree expressions after having posted
	 * equality constraints, i.e., for each new variable, a constraint forcing it to be equal to the corresponding tree
	 * expression
	 * 
	 * @param trees
	 *            an array of tree expressions
	 * @return an array of new (auxiliary) variables representing the specified tree expressions
	 */
	private Var[] replaceByVariables(XNode<IVar>[] trees) {
		if (trees.length == 1)
			return new Var[] { (Var) replaceByVariable(trees[0]) };
		IntToDom doms = i -> {
			Object values = trees[i].possibleValues();
			return values instanceof Range ? api.dom((Range) values) : api.dom((int[]) values);
		};
		// if multiple occurrences of the same variable in a tree, possible problem of reasoning with similar trees?
		boolean similarTrees = trees.length > 1 && Stream.of(trees).allMatch(tree -> tree.listOfVars().size() == tree.vars().length);
		similarTrees = similarTrees && IntStream.range(1, trees.length).allMatch(i -> areSimilar(trees[0], trees[i]));
		Var[] aux = auxVarArray(trees.length, similarTrees ? doms.apply(0) : doms);
		int[][] tuples = null;
		if (similarTrees) {
			Variable[] treeVars = (Variable[]) trees[0].vars();
			if (head.control.intension.toExtension(treeVars, null))
				tuples = new TreeEvaluator(trees[0]).computeTuples(Variable.initDomainValues(treeVars), null);
		}
		for (int i = 0; i < trees.length; i++)
			replacement(aux[i], trees[i], similarTrees, tuples);
		return aux;
	}

	/**
	 * Returns an array of new (auxiliary) variables representing the specified tree expressions after having posted
	 * equality constraints, i.e., for each new variable, a constraint forcing it to be equal to the corresponding tree
	 * expression in the stream
	 * 
	 * @param trees
	 *            a stream of tree expressions
	 * @return an array of new (auxiliary) variables representing the specified tree expressions
	 */
	private Var[] replaceByVariables(Stream<XNode<IVar>> trees) {
		return replaceByVariables(treesToArray(trees));
	}

	private Condition simplifyComplexCondition(Condition condition, Object values) {
		Var aux = auxVar(values); // we introduce an auxiliary variable
		intension(Condition.toNode(aux, condition)); // linking the auxiliary variable to the condition
		return Condition.buildFrom(EQ, aux);
	}

	/**********************************************************************************************
	 *** Posting Constraints
	 *********************************************************************************************/

	/**
	 * Posts the specified constraint, i.e., records it as being a constraint of the problem
	 * 
	 * @param x
	 *            a constraint to be posted
	 * @param classes
	 *            the XCSP3 classes coming with the constraint
	 * @return the posted constraint
	 */
	public final CtrAlone post(Constraint c, TypeClass... classes) {
		// the control about if the constraint must be discarded is done in loadCtr of class XCSP3
		c.num = features.collecting.add(c);
		return ctrEntities.new CtrAlone(c, classes);
	}

	private CtrEntity unimplemented(String msg) {
		return (CtrEntity) Kit.exit("\nunimplemented case for " + msg);
	}

	private CtrEntity unimplementedIf(boolean b, String msg) {
		return b ? unimplemented(msg) : null;
	}

	public Variable[] translate(IVar[] t) {
		return t instanceof Variable[] ? (Variable[]) t : Stream.of(t).map(x -> (Variable) x).toArray(Variable[]::new);
	}

	private Range range(int length) {
		return new Range(length);
	}

	// ************************************************************************
	// ***** Constraint intension
	// ************************************************************************

	// unary
	private Matcher x_relop_k = new Matcher(node(relop, var, val));
	private Matcher k_relop_x = new Matcher(node(relop, val, var));
	private Matcher x_setop_vals = new Matcher(node(setop, var, set_vals));

	// binary
	private Matcher x_relop_y = new Matcher(node(relop, var, var));
	private Matcher x_ariop_y__relop_k = new Matcher(node(relop, node(ariop, var, var), val));
	private Matcher k_relop__x_ariop_y = new Matcher(node(relop, val, node(ariop, var, var)));
	private Matcher x_relop__y_ariop_k = new Matcher(node(relop, var, node(ariop, var, val)));
	private Matcher y_ariop_k__relop_x = new Matcher(node(relop, node(ariop, var, val), var));
	private Matcher logic_y_relop_k__eq_x = new Matcher(node(TypeExpr.EQ, node(relop, var, val), var));
	private Matcher logic_y_relop_k__iff_x = new Matcher(node(IFF, node(relop, var, val), var));
	private Matcher logic_k_relop_y__eq_x = new Matcher(node(TypeExpr.EQ, node(relop, val, var), var));
	private Matcher logic_k_relop_y__iff_x = new Matcher(node(IFF, node(relop, val, var), var));
	private Matcher unalop_x__eq_y = new Matcher(node(TypeExpr.EQ, node(unalop, var), var));
	private Matcher disjonctive = new Matcher(node(TypeExpr.OR, node(TypeExpr.LE, node(ADD, var, val), var), node(TypeExpr.LE, node(ADD, var, val), var)));
	private Matcher x_mul_y__eq_k = new Matcher(node(TypeExpr.EQ, node(MUL, var, var), val));

	// ternary
	private Matcher x_ariop_y__relop_z = new Matcher(node(relop, node(ariop, var, var), var));
	private Matcher z_relop__x_ariop_y = new Matcher(node(relop, var, node(ariop, var, var)));
	private Matcher logic_y_relop_z__eq_x = new Matcher(node(TypeExpr.EQ, node(relop, var, var), var));

	// logic
	private Matcher logic_X__eq_x = new Matcher(node(TypeExpr.EQ, logic_vars, var));
	private Matcher logic_X__ne_x = new Matcher(node(TypeExpr.NE, logic_vars, var));

	// extremum
	private Matcher min_relop = new Matcher(node(relop, min_vars, varOrVal));
	private Matcher max_relop = new Matcher(node(relop, max_vars, varOrVal));

	// sum
	private Matcher add_vars__relop = new Matcher(node(relop, add_vars, varOrVal));
	private Matcher relop__add_vars = new Matcher(node(relop, varOrVal, add_vars));
	private Matcher add_mul_vals__relop = new Matcher(node(relop, add_mul_vals, varOrVal));
	private Matcher add_mul_vars__relop = new Matcher(node(relop, add_mul_vars, varOrVal));
	private Matcher relop__add_mul_vals = new Matcher(node(relop, varOrVal, add_mul_vals));
	private Matcher relop__add_mul_vars = new Matcher(node(relop, varOrVal, add_mul_vars));

	// product
	private Matcher mul_vars__relop = new Matcher(node(relop, mul_vars, val));

	private Condition basicCondition(XNodeParent<IVar> tree) {
		if (!tree.type.isRelationalOperator() || tree.sons.length != 2)
			return null;
		if (tree.sons[0].type.oneOf(VAR, LONG) || tree.sons[1].type.oneOf(VAR, LONG)) {
			int side = tree.sons[1].type.oneOf(VAR, LONG) ? 1 : 0;
			TypeConditionOperatorRel op = side == 0 ? tree.relop(0).arithmeticInversion() : tree.relop(0);
			return tree.sons[side].type == VAR ? new ConditionVar(op, tree.sons[side].var(0)) : new ConditionVal(op, tree.sons[side].val(0));
		}
		return null;
	}

	private boolean mayBeHybrid(XNode<IVar> tree) {
		// TODO accelerate things here (avoid too many tests)
		return x_relop_k.matches(tree) || k_relop_x.matches(tree) || x_setop_vals.matches(tree) || x_relop_y.matches(tree);
	}

	@Override
	public final CtrEntity intension(XNodeParent<IVar> tree) {
		tree = (XNodeParent<IVar>) tree.canonization(); // first, the tree is canonized
		Variable[] scp = (Variable[]) tree.vars(); // keep this statement here, after canonization
		int arity = scp.length;
		// System.out.println("Tree " + tree);

		OptionsIntension options = head.control.intension;
		if (arity == 1) {
			TreeEvaluator evaluator = new TreeEvaluator(tree, symbolic.mapOfSymbols);
			Variable x = (Variable) tree.var(0);
			if (head.mustPreserveUnaryConstraints()) {
				if (!options.toExtension1)
					return post(new ConstraintIntension(this, scp, tree));
				int[] values = x.dom.valuesChecking(v -> evaluator.evaluate(v) != 1); // initially, conflicts
				boolean positive = values.length >= x.dom.size() / 2;
				if (positive)
					values = x.dom.valuesChecking(v -> evaluator.evaluate(v) == 1); // we store supports instead
				return post(new Extension1(this, x, values, positive));
			}
			x.dom.removeValuesAtConstructionTime(v -> evaluator.evaluate(v) != 1);
			features.nRemovedUnaryCtrs++;
			return ctrEntities.new CtrAloneDummy("Removed unary constraint by domain reduction");
		}

		assert Variable.haveSameType(scp);
		if (options.toExtension(scp, tree) && Stream.of(scp).allMatch(x -> x instanceof Var)) {
			features.nConvertedConstraints++;
			return extension(tree);
		}

		if (options.toHybrid) { // TODO section to finalize with various cases
			if (tree.type == TypeExpr.IMP) {
				XNode<IVar> son0 = tree.sons[0], son1 = tree.sons[1];
				if (mayBeHybrid(son0) && mayBeHybrid(son1)) { // TODO and check no shared variables ?
					XNodeParent<IVar> newson0 = XNodeParent.build(son0.type.logicalInversion(), (Object[]) son0.sons);
					HybridTuple ht1 = new HybridTuple((int[]) null, newson0);
					HybridTuple ht2 = new HybridTuple((int[]) null, (XNodeParent<IVar>) son1);
					return hybrid(scp, ht1, ht2);
				}
			} else if (tree.type == TypeExpr.OR && Stream.of(tree.sons).allMatch(son -> mayBeHybrid(son))) {
				// TODO and check no shared variables ?
				Stream<HybridTuple> stream = Stream.of(tree.sons).map(son -> new HybridTuple((int[]) null, (XNodeParent<IVar>) son));
				return hybrid(scp, stream);
			}
		}

		if (arity == 2 && x_mul_y__eq_k.matches(tree)) {
			int k = tree.val(0);
			// we can intercept the cases where k=0 or k=1; below, we can use scp because we are sure
			// that the two variables are different (arity is 2) ; so no need to use tree.arrayOfVars()
			if (k == 0)
				return intension(or(eq(scp[0], 0), eq(scp[1], 0)));
			if (k == 1)
				return forall(range(2), i -> equal(scp[i], 1));
		}

		if (arity == 2 && options.recognizePrimitive2) {
			Constraint c = null;
			if (x_relop_y.matches(tree))
				c = Sub2.buildFrom(this, scp[0], scp[1], tree.relop(0), 0);
			else if (x_ariop_y__relop_k.matches(tree))
				c = Primitive2.buildFrom(this, scp[0], tree.ariop(0), scp[1], tree.relop(0), tree.val(0));
			else if (k_relop__x_ariop_y.matches(tree)) {
				if (tree.val(0) <= 0) {
					Kit.warning("discarded constraint (because useless) : " + tree);
					return null;
				}
				c = Primitive2.buildFrom(this, scp[0], tree.ariop(0), scp[1], tree.relop(0).arithmeticInversion(), tree.val(0));
			} else if (x_relop__y_ariop_k.matches(tree))
				c = Primitive2.buildFrom(this, scp[0], tree.relop(0), scp[1], tree.ariop(0), tree.val(0));
			else if (y_ariop_k__relop_x.matches(tree))
				c = Primitive2.buildFrom(this, scp[1], tree.relop(0).arithmeticInversion(), scp[0], tree.ariop(0), tree.val(0));
			else if (logic_y_relop_k__eq_x.matches(tree) && scp[1].dom.is01())
				c = Reif2.buildFrom(this, scp[1], scp[0], tree.relop(1), tree.val(0));
			else if (logic_y_relop_k__iff_x.matches(tree) && scp[1].dom.is01())
				c = Reif2.buildFrom(this, scp[1], scp[0], tree.relop(0), tree.val(0));
			else if (logic_k_relop_y__eq_x.matches(tree) && scp[1].dom.is01())
				c = Reif2.buildFrom(this, scp[1], scp[0], tree.relop(1).arithmeticInversion(), tree.val(0));
			else if (unalop_x__eq_y.matches(tree))
				c = Primitive2.buildFrom(this, scp[1], tree.unalop(0), scp[0]);
			else if (disjonctive.matches(tree)) {
				Variable[] scp0 = (Variable[]) tree.sons[0].vars(), scp1 = (Variable[]) tree.sons[1].vars();
				if (scp0.length == 2 && scp1.length == 2 && scp0[0] == scp1[1] && scp0[1] == scp1[0]) {
					int k0 = tree.sons[0].val(0), k1 = tree.sons[1].val(0);
					c = new Disjonctive(this, scp0[0], k0, scp[1], k1);
				}
			}
			if (c != null)
				return post(c);
		}
		if (arity == 3 && options.recognizePrimitive3) {
			Constraint c = null;
			if (x_ariop_y__relop_z.matches(tree))
				c = Primitive3.buildFrom(this, scp[0], tree.ariop(0), scp[1], tree.relop(0), scp[2]);
			else if (z_relop__x_ariop_y.matches(tree))
				c = Primitive3.buildFrom(this, scp[1], tree.ariop(0), scp[2], tree.relop(0).arithmeticInversion(), scp[0]);
			else if (logic_y_relop_z__eq_x.matches(tree))
				c = Reif3.buildFrom(this, scp[2], scp[0], tree.relop(1), scp[1]);
			if (c != null)
				return post(c);
		}
		if (options.recognizeReifLogic) {
			Constraint c = null;
			if (logic_X__eq_x.matches(tree)) {
				Variable[] list = IntStream.range(0, scp.length - 1).mapToObj(i -> scp[i]).toArray(Variable[]::new);
				c = ReifLogic.buildFrom(this, scp[scp.length - 1], tree.logop(0), list);
			}
			// TODO other cases to be implemented
			if (c != null)
				return post(c);

		}
		// if (arity >= 2 && tree.type == OR && Stream.of(tree.sons).allMatch(son -> x_relop_k.matches(son))) { }

		if (options.recognizeExtremum) {
			if (min_relop.matches(tree))
				return minimum((Var[]) tree.sons[0].vars(), basicCondition(tree));
			if (max_relop.matches(tree))
				return maximum((Var[]) tree.sons[0].vars(), basicCondition(tree));
		}
		if (options.recognizeSum) {
			if (add_vars__relop.matches(tree) || relop__add_vars.matches(tree)) {
				int side = add_vars__relop.matches(tree) ? 0 : 1;
				Var[] list = (Var[]) tree.sons[side].arrayOfVars();
				return sum(list, Kit.repeat(1, list.length), basicCondition(tree));
			}
			if (add_mul_vals__relop.matches(tree) || relop__add_mul_vals.matches(tree)) {
				int side = add_mul_vals__relop.matches(tree) ? 0 : 1;
				Var[] list = (Var[]) tree.sons[side].arrayOfVars();
				int[] coeffs = Stream.of(tree.sons[side].sons).mapToInt(s -> s.type == VAR ? 1 : s.val(0)).toArray();
				return sum(list, coeffs, basicCondition(tree));
			}
			if (add_mul_vars__relop.matches(tree) || relop__add_mul_vars.matches(tree)) {
				int side = add_mul_vars__relop.matches(tree) ? 0 : 1;
				Var[] list = Stream.of(tree.sons[side].sons).map(s -> s.var(0)).toArray(Var[]::new);
				Var[] coeffs = Stream.of(tree.sons[side].sons).map(s -> s.var(1)).toArray(Var[]::new);
				return sum(list, coeffs, basicCondition(tree));
			}
		}
		if (mul_vars__relop.matches(tree)) {
			Var[] list = (Var[]) tree.arrayOfVars();
			if (tree.relop(0) == EQ && tree.sons[1].type == LONG) {
				Integer k = tree.sons[1].val(0);
				if (k == 0)
					return intension(or(Stream.of(list).map(x -> eq(x, 0))));
				if (k == 1)
					return forall(range(list.length), i -> equal(list[i], 1));
			}
			return product(list, basicCondition(tree));
		}

		boolean b = options.decompose > 0 && scp[0] instanceof VariableInteger && scp.length + 1 >= tree.listOfVars().size();
		// at most a variable occurring twice
		b = b || options.decompose == 2;
		if (b) {
			XNode<IVar>[] sons = tree.sons;
			int nParentSons = 0;
			if (tree.type == TypeExpr.EQ) {
				// we reason with grandsons for avoiding recursive similar changes when making replacements
				for (XNode<IVar> son : sons) {
					if (son instanceof XNodeParent) {
						nParentSons++;
						XNode<IVar>[] grandsons = son.sons;
						boolean modified = false;
						for (int j = 0; j < grandsons.length; j++) {
							if (grandsons[j] instanceof XNodeParent && grandsons[j].type != TypeExpr.SET) {
								grandsons[j] = new XNodeLeaf<>(TypeExpr.VAR, replaceByVariable(grandsons[j]));
								modified = true;
							}
						}
						if (modified)
							return intension(tree);
					}
				}
			}
			if (tree.type != TypeExpr.EQ || nParentSons > 1) {
				// if not EQ or if more than one parent son then we flatten the first parent son
				for (int i = 0; i < sons.length; i++) {
					if (sons[i] instanceof XNodeParent && sons[i].type != TypeExpr.SET) {
						sons[i] = new XNodeLeaf<>(TypeExpr.VAR, replaceByVariable(sons[i]));
						return intension(tree);
					}
				}
			}
		}
		return post(new ConstraintIntension(this, scp, tree));
	}

	// ************************************************************************
	// ***** Converting intension to extension
	// ************************************************************************

	/**
	 * Different ways of converting towards extension
	 */
	private static enum ExtensionMode {
		NO,
		INTENSION,
		EXTENSION, // EXTENSION is for automatic mode (either supports or conflicts)
		EXTENSION_SUPPORTS,
		EXTENSION_CONFLICTS;
	}

	private Converter converter = new Converter() {

		@Override
		public StringBuilder signatureFor(Var[] scp) {
			return Variable.signatureFor((Variable[]) scp);
		}

		@Override
		public int[][] domValuesOf(Var[] scp) {
			return Variable.initDomainValues((Variable[]) scp);
		}

		@Override
		public ModifiableBoolean mode() {
			ExtensionMode exportMode = ExtensionMode.EXTENSION; // later, maybe a
																// control parameter
			return new ModifiableBoolean(exportMode != ExtensionMode.EXTENSION_SUPPORTS && exportMode != ExtensionMode.EXTENSION_CONFLICTS ? null
					: exportMode == ExtensionMode.EXTENSION_SUPPORTS);
		}
	};

	@Override
	protected Converter getConverter() {
		return converter;
	}

	// ************************************************************************
	// ***** Constraint extension
	// ************************************************************************

	private static final Boolean DONT_KNOW = null;

	/**
	 * Posts a unary constraint
	 * 
	 * @param x
	 *            a variable
	 * @param values
	 *            the values considered as supports (i.e., authorized) or conflicts for the variable
	 * @param positive
	 *            if true, specified values are supports; otherwise are conflicts
	 * @return a unary extension constraint
	 */
	public final CtrAlone extension(Variable x, int[] values, boolean positive) {
		assert values.length > 0 && Kit.isStrictlyIncreasing(values) && IntStream.of(values).noneMatch(v -> v == STAR);
		if (head.mustPreserveUnaryConstraints())
			return post(new Extension1(this, x, values, positive));
		// else the unary constraint is definitively taken into consideration by modifying the domain of the variable
		x.dom.removeValuesAtConstructionTime(v -> (Arrays.binarySearch(values, v) < 0) == positive);
		features.nRemovedUnaryCtrs++;
		return null;
	}

	public final CtrAlone extension(IVar[] list, Object[] tuples, boolean positive, Boolean starred) {
		Variable[] scp = translate(list);
		if (tuples.length == 0)
			return post(positive ? new CtrFalse(this, scp, "Extension with 0 support") : new CtrTrue(this, scp, "Extension with 0 conflict"));
		if (list.length == 1) {
			control(starred == null);
			int[][] m = scp[0] instanceof VariableSymbolic ? symbolic.replaceSymbols((String[][]) tuples) : (int[][]) tuples;
			int[] values = Stream.of(m).mapToInt(t -> t[0]).toArray();
			return extension(scp[0], values, positive);
		}
		return post(ConstraintExtension.buildFrom(this, scp, tuples, positive, starred));
	}

	@Override
	public final CtrAlone extension(Var[] list, int[][] tuples, boolean positive) {
		return extension(list, tuples, positive, DONT_KNOW);
	}

	@Override
	public final CtrAlone extension(VarSymbolic[] list, String[][] tuples, boolean positive) {
		return extension(list, tuples, positive, DONT_KNOW);
	}

	@Override
	public final CtrAlone extension(Var[] list, AbstractTuple[] tuples, boolean positive) {
		unimplementedIf(!positive, "negative hybrid tables not implemented");
		return hybrid(list, Stream.of(tuples).filter(t -> HybridTuple.isValid(t, list)).map(t -> HybridTuple.convert(t, list)));
	}

	// ************************************************************************
	// ***** Constraints regular and mdd
	// ************************************************************************

	@Override
	public final CtrAlone regular(Var[] list, Automaton automaton) {
		unimplementedIf(!automaton.isDeterministic(), "non deterministic automaton");
		return post(new CMDDO(this, translate(list), automaton));
	}

	@Override
	public final CtrAlone mdd(Var[] list, Transition[] transitions) {
		return post(new CMDDO(this, translate(list), transitions));
	}

	public final CtrAlone mdd(Var[] list, int[][] tuples) {
		return post(new CMDDO(this, translate(list), tuples));
	}

	// ************************************************************************
	// ***** Constraints AllDifferent and DistinctVectors
	// ************************************************************************

	private CtrEntity allDifferent(Variable[] scp) {
		if (scp.length <= 1) {
			Color.ORANGE.println("Warning: AllDifferent with a scope of length " + scp.length + " : " + Kit.join(scp));
			return null;
		}
		if (scp.length == 2)
			return different(scp[0], scp[1]);

		switch (head.control.global.allDifferent) {
		case 0:
			if (head.control.global.permutation && AllDifferentPermutation.isElligible(scp))
				return post(new AllDifferentPermutation(this, scp));
			return post(new AllDifferentComplete(this, scp));
		case 1:
			return forall(range(scp.length).range(scp.length), (i, j) -> {
				if (i < j)
					different(scp[i], scp[j]);
			});
		case 2:
			return post(new AllDifferentWeak(this, scp, false));
		// return post(new AllDifferentExceptWeak(this, scp, null, false));
		case 22:
			return post(new AllDifferentWeak(this, scp, true));
		// return post(new AllDifferentExceptWeak(this, scp, null, true));
		case 3:
			return post(new AllDifferentCounting(this, scp));
		// case 4: return post(new AllDifferentBound(this, scp));
		default:
			throw new AssertionError("Invalid mode");
		}
	}

	@Override
	public final CtrEntity allDifferent(Var[] list) {
		return allDifferent(translate(list));
	}

	@Override
	public final CtrEntity allDifferent(VarSymbolic[] list) {
		return allDifferent(translate(list));
	}

	private CtrAlone binaryDifferentExcept(Variable x, Variable y, int[] exceptValues) {
		int[] t = x.dom.valuesChecking(v -> !Kit.isPresent(v, exceptValues) && y.dom.containsValue(v));
		return extension(vars(x, y), IntStream.of(t).mapToObj(v -> new int[] { v, v }).toArray(int[][]::new), false, false);
	}

	@Override
	public final CtrEntity allDifferent(Var[] list, int[] exceptValues) {
		control(exceptValues.length >= 1 && Kit.isStrictlyIncreasing(exceptValues));
		Variable[] scp = translate(list);
		if (scp.length <= 1) {
			Color.ORANGE.println("Warning: AllDifferentExcept with a scope of length " + scp.length + " : " + Kit.join(scp));
			return null;
		}
		if (scp.length == 2)
			return binaryDifferentExcept(scp[0], scp[1], exceptValues);

		switch (head.control.global.allDifferentExcept) {
		case 0: // TODO is it efficient? the three approaches should be experimentally tested
			Set<Integer> values = Variable.setOfvaluesIn(scp);
			for (int v : exceptValues)
				values.remove(v);
			return post(new Cardinality(this, scp, values.stream().mapToInt(i -> i).sorted().toArray(), 0, 1));
		case 1: // decomposition
			return forall(range(scp.length).range(scp.length), (i, j) -> {
				if (i < j)
					binaryDifferentExcept(scp[i], scp[j], exceptValues);
			});
		case 2:
			return post(new AllDifferentExceptWeak(this, scp, exceptValues, false));
		case 22:
			return post(new AllDifferentExceptWeak(this, scp, exceptValues, true));
		default:
			throw new AssertionError("Invalid mode");
		}
	}

	private CtrEntity distinctVectors(Variable[] t1, Variable[] t2) {
		control(t1.length == t2.length);
		boolean normalized = IntStream.range(0, t1.length).allMatch(i -> t1[i] != t2[i]);
		Variable[] list1 = normalized ? t1 : IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t1[i]).toArray(Variable[]::new);
		Variable[] list2 = normalized ? t2 : IntStream.range(0, t2.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t2[i]).toArray(Variable[]::new);

		if (head.control.global.distinctVectors == 0)
			return post(new DistinctLists(this, list1, list2));
		if (head.control.global.hybrid)
			return post(CHybrid.distinctVectors(this, list1, list2));
		return api.disjunction(IntStream.range(0, list1.length).mapToObj(i -> api.ne(list1[i], list2[i])));
		// return extension(vars(list1, list2), Table.starredDistinctVectors(list1, list2), true); // TODO problem if
		// several occurrences of the same variable
	}

	/**
	 * Builds a DistinctVectors constraint. The tuple of values corresponding to the assignment of the variables in the
	 * array specified as first parameter must be different from the tuple of values corresponding to the assignment of
	 * the variables in the array specified as second parameter.
	 */
	private CtrEntity distinctVectors(Variable[][] lists) {
		return forall(range(lists.length).range(lists.length), (i, j) -> {
			if (i < j) {
				distinctVectors(lists[i], lists[j]);
			}
		});
	}

	@Override
	public final CtrEntity allDifferentList(Var[]... lists) {
		control(lists.length >= 2);
		Variable[][] m = lists instanceof Variable[][] ? (Variable[][]) lists : Stream.of(lists).map(t -> translate(t)).toArray(Variable[][]::new);
		return m.length == 2 ? distinctVectors(m[0], m[1]) : distinctVectors(m);
	}

	@Override
	public final CtrEntity allDifferentList(Var[][] lists, int[][] except) {
		control(lists.length >= 2);
		Variable[][] m = lists instanceof Variable[][] ? (Variable[][]) lists : Stream.of(lists).map(t -> translate(t)).toArray(Variable[][]::new);
		// TODO : for the moment, only possibility of starred tables
		return forall(range(m.length).range(m.length), (i, j) -> {
			if (i < j) {
				int[][] table = Table.starredDistinctVectors(m[i], m[j], except);
				extension(vars(m[i], m[j]), table, true);
			}
		});
	}

	@Override
	public final CtrEntity allDifferentMatrix(Var[][] matrix) {
		CtrArray ctrSet1 = forall(range(matrix.length), i -> allDifferent(matrix[i]));
		CtrArray ctrSet2 = forall(range(matrix[0].length), i -> allDifferent(api.columnOf(matrix, i)));
		return ctrSet1.append(ctrSet2);
	}

	public final CtrEntity allDifferentMatrix(Var[][] matrix, int[] exceptValues) {
		CtrArray ctrSet1 = forall(range(matrix.length), i -> allDifferent(matrix[i], exceptValues));
		CtrArray ctrSet2 = forall(range(matrix[0].length), i -> allDifferent(api.columnOf(matrix, i), exceptValues));
		return ctrSet1.append(ctrSet2);
	}

	@Override
	public CtrEntity allDifferent(XNode<IVar>[] trees) {
		return allDifferent(replaceByVariables(trees));
	}

	// ************************************************************************
	// ***** Constraint allEqual
	// ************************************************************************

	@Override
	public final CtrEntity allEqual(Var... scp) {
		// note that using a table on large instances of Domino is very expensive
		// using a smart table is also very expensive: return post(CSmart.allEqual(this, translate(scp)));
		return post(new AllEqual(this, translate(scp)));
	}

	public CtrEntity allEqual(XNode<IVar>[] trees) {
		return allEqual(replaceByVariables(trees));
	}

	@Override
	public final CtrEntity allEqual(VarSymbolic... scp) {
		return unimplemented("AllEqual");
	}

	@Override
	public final CtrEntity allEqualList(Var[]... lists) {
		return unimplemented("AllEqual");
	}

	// ************************************************************************
	// ***** Constraint ordered/lexicographic
	// ************************************************************************

	/**
	 * Ensures that the specified array of variables is ordered according to the specified operator, when considering
	 * the associated lengths. We must have x[i]+lengths[i] op x[i+1]. Can be decomposed into a sequence of binary
	 * constraints.
	 */
	@Override
	public final CtrEntity ordered(Var[] list, int[] lengths, TypeOperatorRel op) {
		control(list.length == lengths.length + 1);
		return forall(range(list.length - 1),
				i -> post(Sub2.buildFrom(this, (Variable) list[i], (Variable) list[i + 1], op.toConditionOperator(), -lengths[i])));
	}

	/**
	 * Ensures that the specified array of variables is ordered according to the specified operator, when considering
	 * the associated lengths. We must have list[i]+lengths[i] op list[i+1]. Can be decomposed into a sequence of binary
	 * constraints.
	 */
	@Override
	public final CtrEntity ordered(Var[] list, Var[] lengths, TypeOperatorRel op) {
		control(list.length == lengths.length + 1);
		return forall(range(list.length - 1),
				i -> post(Add3.buildFrom(this, (Variable) list[i], (Variable) lengths[i], op.toConditionOperator(), (Variable) list[i + 1])));
	}

	public final CtrEntity lex(Var[] list, int[] limit, TypeOperatorRel op) {
		return post(Lexicographic.buildFrom(this, translate(list), limit, op));
	}

	/**
	 * Builds and returns a Lexicographic constraint. The tuple of values corresponding to the assignment of the
	 * variables in the array specified as first parameter must be before the tuple of values corresponding to the
	 * assignment of the variables in the array specified as second parameter. The meaning of the relation "before" is
	 * given by the value of the specified operator that must be one value among LT, LE, GT, and GE.
	 */
	private final CtrAlone lexSimple(Var[] t1, Var[] t2, TypeOperatorRel op) {
		return post(Lexicographic.buildFrom(this, translate(t1), translate(t2), op));
	}

	@Override
	public final CtrEntity lex(Var[][] lists, TypeOperatorRel op) {
		return forall(range(lists.length - 1), i -> lexSimple(lists[i], lists[i + 1], op));
	}

	@Override
	public final CtrEntity lexMatrix(Var[][] matrix, TypeOperatorRel op) {
		forall(range(matrix.length - 1), i -> lexSimple(matrix[i], matrix[i + 1], op));
		return forall(range(matrix[0].length - 1), j -> lexSimple(api.columnOf(matrix, j), api.columnOf(matrix, j + 1), op));
	}

	private CtrEntity precedence(Var[] list, int s, int t) {
		different(list[0], t);
		return forall(new Range(1, list.length), i -> disjunction(api.ne(list[i], t), IntStream.range(0, i).mapToObj(j -> api.eq(list[j], s))));
	}

	public final CtrEntity precedence(Var[] list) {
		return post(new Precedence(this, translate(list)));
	}

	@Override
	public final CtrEntity precedence(Var[] list, int[] values, boolean covered) {
		return post(new Precedence(this, translate(list), values, covered));
		// return forall(range(values.length - 1), i -> precedence(list, values[i], values[i + 1]));
	}

	// ************************************************************************
	// ***** Constraints Sum
	// ************************************************************************

	public static class Term implements Comparable<Term> {
		@Override
		public int compareTo(Term term) {
			return Long.compare(coeff, term.coeff);
		}

		public long coeff;
		public Object obj; // typically, a variable or a tree

		public Term(long coeff, Object obj) {
			this.coeff = coeff;
			this.obj = obj;
		}

		@Override
		public String toString() {
			return coeff + "*" + obj;
		}
	}

	private CtrEntity sum(Variable[] list, int[] coeffs, TypeConditionOperatorRel op, long limit, boolean inversable) {
		// grouping together several occurrences of the same variables and discarding terms of coefficient 0
		Term[] terms = new Term[list.length];
		for (int i = 0; i < terms.length; i++)
			terms[i] = new Term(coeffs == null ? 1 : coeffs[i], list[i]);

		if (!Variable.areAllDistinct(list)) {
			Set<Entry<Object, Long>> entries = Stream.of(terms).collect(groupingBy(t -> t.obj, summingLong((Term t) -> (int) t.coeff))).entrySet();
			terms = entries.stream().map(e -> new Term(e.getValue(), e.getKey())).toArray(Term[]::new);
			log.info("Sum constraint with several ocurrences of the same variable");
		}
		// we discard terms of coeff 0 and sort them
		terms = Stream.of(terms).filter(t -> t.coeff != 0).sorted().toArray(Term[]::new);

		list = Stream.of(terms).map(t -> t.obj).toArray(Variable[]::new);
		control(Stream.of(terms).allMatch(t -> Utilities.isSafeInt(t.coeff)));
		coeffs = Stream.of(terms).mapToInt(t -> (int) t.coeff).toArray();

		// we reverse if possible (to have some opportunity to have only coeffs equal to 1)
		if (inversable && coeffs[0] == -1 && coeffs[coeffs.length - 1] == -1) { // if only -1 since sorted
			Arrays.fill(coeffs, 1);
			op = op.arithmeticInversion();
			limit = -limit;
		}
		if (list.length == 1) {
			control(coeffs[0] != 0);
			return postExprSubjectToCondition(coeffs[0] != 1 ? api.mul(list[0], coeffs[0]) : list[0], Condition.buildFrom(op, limit));
		}

		boolean only1 = coeffs[0] == 1 && coeffs[coeffs.length - 1] == 1; // if only 1 since sorted
		if (op == EQ) {
			boolean postTwoConstraints = head.control.global.eqDecForSum;
			if (postTwoConstraints) {
				if (only1) {
					post(new SumSimpleLE(this, list, limit));
					post(new SumSimpleGE(this, list, limit));
				} else {
					post(new SumWeightedLE(this, list, coeffs, limit));
					post(new SumWeightedGE(this, list, coeffs, limit));
				}
				return null; // null because several constraints // TODO returning a special value?
				// return addCtr(new CtrExtensionMDD(this, list, coeffs, new Range(limit, limit+1))));
			}
		}

		if (only1) {
			// TODO if op != NE && Variable.areInitiallyBoolean(list), return atMost, atLeast or exactly?
			// not sure at all that it may be more efficient
			return post(SumSimple.buildFrom(this, list, op, limit));
		}
		return post(SumWeighted.buildFrom(this, list, coeffs, op, limit));
	}

	private CtrEntity sum(IVar[] list, int[] coeffs, TypeConditionOperatorRel op, long limit) {
		return sum(translate(list), coeffs, op, limit, true);
	}

	@Override
	public final CtrEntity sum(Var[] list, int[] coeffs, Condition condition) {
		control(list.length > 0, "A constraint sum is posted with a scope of 0 variable");
		control(Stream.of(list).noneMatch(x -> x == null), "A variable is null");
		control(list.length == coeffs.length, "the number of variables is different from the number of coefficients");

		Object rightTerm = condition.rightTerm(); // a constant, a variable, a range or an int array according to the
													// type of the condition

		// we remove terms with coefficient 0
		if (IntStream.of(coeffs).anyMatch(v -> v == 0)) {
			int[] copy = coeffs.clone(); // to be able to use streams
			coeffs = api.selectFromIndexing(coeffs, i -> copy[i] != 0);
			control(coeffs.length > 0);
			list = api.select(list, i -> copy[i] != 0);
		}

		// then, we handle the case where there is only one term (no need for a sum constraint)
		if (list.length == 1) {
			assert coeffs[0] != 0;
			if (condition instanceof ConditionSet) // rightTerm is either an object Range or an int array
				rightTerm = api.set(rightTerm);
			XNodeParent<IVar> tree = build(condition.operatorTypeExpr(), coeffs[0] == 1 ? list[0] : api.mul(list[0], coeffs[0]), rightTerm);
			return extension(tree); // we directly generate a table constraint because the arity is 1 or 2
		}

		// then, we handle the cases when the condition involves a set operator (IN or NOTIN)
		if (condition instanceof ConditionSet) {
			TypeConditionOperatorSet op = ((ConditionSet) condition).operator;
			if (op == TypeConditionOperatorSet.NOTIN) {
				if (condition instanceof ConditionIntvl)
					for (int v : ((Range) rightTerm))
						sum(list, coeffs, NE, v);
				else
					for (int v : (int[]) rightTerm)
						sum(list, coeffs, NE, v);
			} else { // IN
				// boolean mdd = false; // hard coding for the moment
				// if (mdd)
				// return post(new CMDDO(this, translate(list), coeffs, rightTerm));
				if (condition instanceof ConditionIntvl) {
					sum(list, coeffs, GE, ((Range) rightTerm).start);
					sum(list, coeffs, LE, ((Range) rightTerm).stop - 1);
				} else {
					int[] t = (int[]) rightTerm;
					int min = t[0], max = t[t.length - 1];
					sum(list, coeffs, GE, min);
					sum(list, coeffs, LE, max);
					for (int v = min + 1, index = 1; v < max; v++) {
						if (v < t[index])
							sum(list, coeffs, NE, v);
						else
							index++;
					}
				}
			}
			return null; // null because several constraints // TODO returning a special value?
		}
		// finally, we handle the cases where the condition involves a relational operator
		TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
		return condition instanceof ConditionVal ? sum(list, coeffs, op, (long) rightTerm) : sum(vars(list, (Variable) rightTerm), api.vals(coeffs, -1), op, 0);
	}

	@Override
	public final CtrEntity sum(Var[] list, Var[] coeffs, Condition condition) {
		control(list.length > 0, "A constraint sum is posted with a scope of 0 variable");
		assert Stream.of(list).noneMatch(x -> x == null) && Stream.of(coeffs).noneMatch(x -> x == null) : "A variable is null in these arrays";
		control(list.length == coeffs.length, "The number of variables is different from the number of coefficients");

		// we check first if we can handle a Boolean scalar constraint
		if (condition instanceof ConditionRel && Variable.areAllInitiallyBoolean(translate(list)) && Variable.areAllInitiallyBoolean(translate(coeffs))) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Object rightTerm = condition.rightTerm();
			if (list.length == 1) { // no need to generate a specialized constraint in this case
				XNodeParent<IVar> tree = build(condition.operatorTypeExpr(), api.mul(list[0], coeffs[0]), rightTerm);
				return intension(tree);
			}
			if (condition instanceof ConditionVal && op != NE)
				return post(SumScalarBooleanCst.buildFrom(this, translate(list), translate(coeffs), op, safeInt((long) rightTerm)));
			if (condition instanceof ConditionVar && op != NE && op != EQ)
				return post(SumScalarBooleanVar.buildFrom(this, translate(list), translate(coeffs), op, (Variable) rightTerm));
		}

		Var[] aux = replaceByVariables(IntStream.range(0, list.length).mapToObj(i -> api.mul(list[i], coeffs[i])));
		return sum(aux, Kit.repeat(1, list.length), condition);
	}

	@Override
	public CtrEntity sum(XNode<IVar>[] trees, int[] coeffs, Condition condition) {
		control(trees.length > 0, "A constraint sum is posted with a scope of 0 variable");

		if (coeffs != null && IntStream.of(coeffs).anyMatch(c -> c == 0)) { // we discard useless terms, if any
			int[] clone = coeffs.clone(); // to be able to use streams
			return sum(IntStream.range(0, trees.length).filter(i -> clone[i] != 0).mapToObj(i -> trees[i]).toArray(XNode[]::new),
					IntStream.of(coeffs).filter(c -> c != 0).toArray(), condition);
		}
		if (head.control.global.viewForSum && condition instanceof ConditionRel) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Object rightTerm = condition.rightTerm();
			if (op != NE && Stream.of(trees).allMatch(tree -> tree.type.isPredicateOperator() && tree.vars().length == 1)) {
				if (condition instanceof ConditionVar) {
					Term[] terms = new Term[trees.length + 1];
					for (int i = 0; i < trees.length; i++)
						terms[i] = new Term(coeffs == null ? 1 : coeffs[i], trees[i]);
					terms[terms.length - 1] = new Term(-1, new XNodeLeaf<>(VAR, (Variable) rightTerm));
					// we discard terms of coeff 0 and sort them
					terms = Stream.of(terms).filter(t -> t.coeff != 0).sorted().toArray(Term[]::new);
					XNode<IVar>[] tt = Stream.of(terms).map(t -> t.obj).toArray(XNode[]::new);
					control(Stream.of(terms).allMatch(t -> Utilities.isSafeInt(t.coeff)));
					coeffs = Stream.of(terms).mapToInt(t -> (int) t.coeff).toArray();
					return post(SumViewWeighted.buildFrom(this, tt, coeffs, op, 0));
				} else if (condition instanceof ConditionVal) {
					return post(SumViewWeighted.buildFrom(this, trees, coeffs, op, (long) rightTerm));
				}
			}
		}
		if (coeffs == null)
			coeffs = Kit.repeat(1, trees.length);
		return sum(replaceByVariables(trees), coeffs, condition);
	}

	private CtrEntity sum(XNode<IVar>[] trees, Condition condition) {
		return sum(trees, null, condition);
	}

	private CtrEntity sum(Stream<XNode<IVar>> trees, int[] coeffs, Condition condition) {
		return sum(treesToArray(trees), coeffs, condition);
	}

	private CtrEntity sum(Stream<XNode<IVar>> trees, Condition condition) {
		return sum(trees, null, condition);
	}

	// ************************************************************************
	// ***** Constraint product
	// ************************************************************************

	public final CtrEntity product(Var[] list, Condition condition) {
		if (condition instanceof ConditionRel) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Object rightTerm = condition.rightTerm();
			Variable[] scp = translate(clean(list));
			if (condition instanceof ConditionVal)
				return post(ProductSimple.buildFrom(this, scp, op, (long) rightTerm));
		}
		return unimplemented("product");
	}

	// ************************************************************************
	// ***** Constraint count
	// ************************************************************************

	private CtrEntity atLeast(VariableInteger[] list, int value, int k) {
		assert 0 <= k && k <= list.length;
		if (k == 0)
			return ctrEntities.new CtrAloneDummy("atleast witk k = 0");
		if (k == list.length)
			return instantiation(list, value);
		return post(k == 1 ? new AtLeast1(this, list, value) : new AtLeastK(this, list, value, k));
	}

	private CtrEntity atMost(VariableInteger[] list, int value, int k) {
		assert 0 <= k && k <= list.length;
		if (k == 0)
			return refutation(list, value);
		if (k == list.length)
			return ctrEntities.new CtrAloneDummy("atMost with k = scp.length");
		return post(k == 1 ? new AtMost1(this, list, value) : new AtMostK(this, list, value, k));
	}

	private CtrEntity exactly(VariableInteger[] list, int value, int k) {
		if (k == 0)
			return refutation(list, value);
		if (k == list.length)
			return instantiation(list, value);
		return post(k == 1 ? new Exactly1(this, list, value) : new ExactlyK(this, list, value, k));
	}

	private CtrEntity count(VariableInteger[] list, int[] values, TypeConditionOperatorRel op, long limit) {
		int l = Utilities.safeInt(limit);
		control(0 <= l && l <= list.length);
		if (values.length == 1) {
			int value = values[0];
			VariableInteger[] scp = Stream.of(list).filter(x -> x.dom.containsValue(value) && x.dom.size() > 1).toArray(VariableInteger[]::new);
			int k = l - (int) Stream.of(list).filter(x -> x.dom.containsOnlyValue(value)).count();
			control(scp.length > 0 && 0 <= k && k <= scp.length, Kit.join(scp) + " " + k);
			if (op == LT)
				return atMost(scp, value, k - 1);
			if (op == LE)
				return atMost(scp, value, k);
			if (op == GE)
				return atLeast(scp, value, k);
			if (op == GT)
				return atLeast(scp, value, k + 1);
			if (op == EQ)
				return exactly(scp, value, k);
			control(op == NE && 0 < k && k < scp.length);
			Var aux = auxVar(IntStream.range(0, scp.length + 1).filter(i -> i != k).toArray());
			return count(scp, values, Condition.buildFrom(EQ, aux));
		}
		if (op == EQ) {
			if (l == list.length)
				return forall(range(list.length), i -> intension(in(list[i], set(values))));
			return post(new Among(this, list, values, l));
		}
		return null; // so as to handle it differently after the call
	}

	@Override
	public final CtrEntity count(Var[] list, int[] values, Condition condition) {
		VariableInteger[] scp = Stream.of(list).filter(x -> x != null && ((Variable) x).dom.overlapWith(values)).toArray(VariableInteger[]::new);
		control(scp.length > 0, "A constraint Count is posted with an empty scope");
		if (condition instanceof ConditionRel) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Object rightTerm = condition.rightTerm();
			if (condition instanceof ConditionVal) {
				CtrEntity ce = count(scp, values, op, (long) rightTerm);
				if (ce != null)
					return ce;
			} else if (op == EQ) {
				if (values.length == 1)
					return post(new ExactlyVarK(this, scp, values[0], (Variable) rightTerm));
				return sum(Stream.of(scp).map(x -> in(x, set(values))), condition);
			}
		}
		return count(scp, values, simplifyComplexCondition(condition, range(scp.length + 1)));
	}

	public final CtrEntity count(XNode<IVar>[] trees, int[] values, Condition condition) {
		return count(replaceByVariables(trees), values, condition);
	}

	@Override
	public final CtrEntity count(Var[] list, Var[] values, Condition condition) {
		control(list.length > 0, "A constraint Count is posted with an empty scope");
		// TODO should we handle the case 'list.length == 1' differently ?
		Variable[] vals = translate(clean(values));
		control(vals.length > 0, "A constraint Count is posted with no value");
		if (vals.length == 1)
			return sum(Stream.of(list).map(x -> eq(x, vals[0])), condition);
		return sum(Stream.of(list).map(x -> in(x, set((Object[]) vals))), condition);
	}

	public final CtrEntity count(XNode<IVar>[] trees, Var[] values, Condition condition) {
		return count(replaceByVariables(trees), values, condition);
	}

	// ************************************************************************
	// ***** Constraint nValues
	// ************************************************************************

	@Override
	public CtrEntity nValues(Var[] list, Condition condition) {
		Variable[] scp = translate(clean(list));
		if (condition instanceof ConditionRel) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Object rightTerm = condition.rightTerm();
			Constraint c = condition instanceof ConditionVal ? NValuesCst.buildFrom(this, scp, op, (long) rightTerm)
					: NValuesVar.buildFrom(this, scp, op, (Variable) rightTerm);
			if (c != null)
				return post(c);
		}
		return nValues((Var[]) scp, simplifyComplexCondition(condition, range(scp.length + 1)));
	}

	public CtrEntity nValues(XNode<IVar>[] trees, Condition condition) {
		return nValues(replaceByVariables(trees), condition);
	}

	@Override
	public CtrEntity nValues(Var[] list, Condition condition, int[] exceptValues) {
		return unimplemented("nValues");
	}

	// ************************************************************************
	// ***** Constraint cardinality
	// ************************************************************************

	private CtrArray postClosed(Variable[] list, int[] values) {
		return forall(range(list.length), i -> {
			if (!list[i].dom.initiallySubsetOf(values))
				extension(list[i], api.select(values, v -> list[i].dom.containsValue(v)), true);
		});
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, int[] occurs) {
		// int limit = Utilities.safeInt(IntStream.range(0, values.length).mapToLong(i -> Utilities.safeInt(values[i] *
		// (long) occurs[i], true)).sum(), true);
		control(values.length == occurs.length);
		Variable[] scp = translate(clean(list));
		boolean closed = Stream.of(list).allMatch(x -> ((Variable) x).dom.enclose(values));
		if (!closed && mustBeClosed) {
			// sum(list, Kit.repeat(1, list.length), Condition.buildFrom(EQ, limit));
			postClosed(scp, values);
			closed = true;
		}
		// else sum(list, Kit.repeat(1, list.length), Condition.buildFrom(GE, limit));
		if (closed && IntStream.of(occurs).allMatch(v -> v == 1))
			return allDifferent(list);
		return post(new Cardinality(this, scp, values, occurs));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, int[] occursMin, int[] occursMax) {
		control(values.length == occursMin.length && values.length == occursMax.length);
		Variable[] scp = translate(clean(list));
		if (mustBeClosed)
			postClosed(scp, values);
		return post(new Cardinality(this, scp, values, occursMin, occursMax));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, Var[] occurs) {
		control(values.length == occurs.length && Stream.of(occurs).noneMatch(x -> x == null));
		Variable[] scp = translate(clean(list));
		if (mustBeClosed)
			postClosed(scp, values);
		// TODO should we filer variables of scp not involving values[i]?
		return forall(range(values.length), i -> {
			Variable[] filteredScp = Stream.of(scp).filter(x -> x.dom.containsValue(values[i])).toArray(Variable[]::new);
			control(filteredScp.length > 1);
			post(new ExactlyVarK(this, filteredScp, values[i], (Variable) occurs[i]));
		});
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, int[] occurs) {
		control(values.length == occurs.length && Stream.of(values).noneMatch(x -> x == null));
		return unimplemented("cardinality");
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, Var[] occurs) {
		control(values.length == occurs.length && Stream.of(values).noneMatch(x -> x == null) && Stream.of(occurs).noneMatch(x -> x == null));
		return unimplemented("cardinality");
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, int[] occursMin, int[] occursMax) {
		control(values.length == occursMin.length && values.length == occursMax.length && Stream.of(values).noneMatch(x -> x == null));
		return unimplemented("cardinality");
	}

	// ************************************************************************
	// ***** Constraint minimum/maximum
	// ************************************************************************

	private final CtrEntity extremum(Var[] list, Condition condition, boolean minimum) {
		Variable[] scp = translate(clean(list));
		if (condition instanceof ConditionRel) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Object rightTerm = condition.rightTerm();
			Constraint c = null;
			if (condition instanceof ConditionVal) {
				if (scp.length == 1)
					return intension(build(op.toExpr(), scp[0], (long) rightTerm));
				c = ExtremumCst.buildFrom(this, scp, op, (long) rightTerm, minimum);
			} else if (op == EQ) {
				Variable y = (Variable) rightTerm;
				if (scp.length == 1)
					return equal(scp[0], y);
				if (Stream.of(scp).anyMatch(x -> x == y))
					return forall(range(scp.length), i -> {
						if (y != scp[i])
							if (minimum)
								lessEqual(y, scp[i]);
							else
								greaterEqual(y, scp[i]);
					});
				if (head.control.global.hybrid)
					c = minimum ? CHybrid.minimum(this, scp, y) : CHybrid.maximum(this, scp, y);
				else
					c = minimum ? new Minimum(this, scp, y) : new Maximum(this, scp, y);
			}
			if (c != null)
				return post(c);
		}
		int lb = Utilities.safeInt(minimum ? MinimumCst.minFirstInitialValues(scp) : MaximumCst.maxFirstInitialValues(scp));
		int ub = Utilities.safeInt(minimum ? MinimumCst.minLastInitialValues(scp) : MaximumCst.maxLastInitialValues(scp));
		return extremum((Var[]) scp, simplifyComplexCondition(condition, new Range(lb, ub + 1)), minimum);
	}

	private final CtrEntity extremum(Var[] list, int startIndex, Var index, TypeRank rank, Condition condition, boolean minimum) {
		return unimplemented(minimum ? "minimum" : "maximum");
	}

	@Override
	public final CtrEntity minimum(Var[] list, Condition condition) {
		return extremum(list, condition, true);
	}

	@Override
	public final CtrEntity minimum(Var[] list, int startIndex, Var index, TypeRank rank) {
		return extremum(list, startIndex, index, rank, null, true);
	}

	@Override
	public final CtrEntity minimum(Var[] list, int startIndex, Var index, TypeRank rank, Condition condition) {
		return extremum(list, startIndex, index, rank, condition, true);
	}

	@Override
	public final CtrEntity minimum(XNode<IVar>[] trees, Condition condition) {
		return minimum(replaceByVariables(trees), condition);
	}

	@Override
	public final CtrEntity maximum(final Var[] list, Condition condition) {
		return extremum(list, condition, false);
	}

	@Override
	public final CtrEntity maximum(Var[] list, int startIndex, Var index, TypeRank rank) {
		return extremum(list, startIndex, index, rank, null, false);
	}

	@Override
	public final CtrEntity maximum(Var[] list, int startIndex, Var index, TypeRank rank, Condition condition) {
		return extremum(list, startIndex, index, rank, condition, false);
	}

	@Override
	public final CtrEntity maximum(XNode<IVar>[] trees, Condition condition) {
		return maximum(replaceByVariables(trees), condition);
	}

	// ************************************************************************
	// ***** Constraint minimumArg/maximumArg
	// ************************************************************************

	final CtrEntity maximumArg(Var[] list, TypeRank rank, Condition condition) {
		unimplementedIf(!(condition instanceof ConditionVar && (((ConditionVar) condition).operator) == EQ), "maximumArg");
		return post(new MaximumArg(this, translate(list), (Variable) ((ConditionVar) condition).x, rank));
	}

	final CtrEntity maximumArg(XNode<IVar>[] trees, TypeRank rank, Condition condition) {
		return maximumArg(replaceByVariables(trees), rank, condition);
	}

	final CtrEntity minimumArg(Var[] list, TypeRank rank, Condition condition) {
		unimplementedIf(!(condition instanceof ConditionVar && (((ConditionVar) condition).operator) == EQ), "minimumArg");
		return post(new MinimumArg(this, translate(list), (Variable) ((ConditionVar) condition).x, rank));
	}

	final CtrEntity minimumArg(XNode<IVar>[] trees, TypeRank rank, Condition condition) {
		return minimumArg(replaceByVariables(trees), rank, condition);
	}

	// ************************************************************************
	// ***** Constraint element
	// ************************************************************************

	@Override
	public final CtrEntity element(Var[] list, Condition condition) {
		// this corresponds to constraint Member
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			int k = safeInt(((ConditionVal) condition).k);
			if (op == EQ)
				return atLeast((VariableInteger[]) translate(list), k, 1);
			if (op == NE)
				return forall(range(list.length), i -> different(list[i], k));
		}
		if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
			Variable x = (Variable) ((ConditionVar) condition).x;
			if (op == EQ)
				return extension(vars(list, x), Table.starredMember(translate(list), x), true);
			if (op == NE)
				return forall(range(list.length), i -> different(list[i], x));
		}

		// TODO for LT, LE, GE and GT, posting minimum or maximum constraints if ConditionRel?
		// for EQ - VAR using sentinelVal1, sentinelVal2 (for two values in dom(value)),
		// and sentinelVar1,sentinelVar2 for two variables in list ?
		return unimplemented("element");
	}

	private CtrAlone element(Var[] list, Var index, int value) {
		if (head.control.global.starred)
			return extension(vars(index, list), Table.starredElement(translate(list), (Variable) index, value), true);
		return post(new ElementCst(this, translate(list), (Variable) index, value));
	}

	private CtrAlone element(Var[] list, Var index, Var value) {
		if (index == value) {
			control(Utilities.indexOf(value, list) == -1);
			Var[] scp = vars(list, value);
			return extension(scp, Table.starredElement(translate(list), (Variable) index), true);
		}
		if (head.control.global.hybrid)
			return post(CHybrid.element(this, translate(list), (Variable) index, (Variable) value));
		if (head.control.global.starred) {
			// TODO controls (for example index != value and index not in list?
			Var[] scp = Utilities.indexOf(value, list) == -1 ? vars(index, list, value) : vars(index, list);
			return extension(scp, Table.starredElement(translate(list), (Variable) index, (Variable) value), true);
		}
		return post(new ElementVar(this, translate(list), (Variable) index, (Variable) value));
	}

	private CtrEntity postExprSubjectToCondition(Object obj, Condition condition) {
		if (condition instanceof ConditionRel)
			return intension(XNodeParent.build(((ConditionRel) condition).operator.toExpr(), obj, condition.rightTerm()));
		if (condition instanceof ConditionIntset) {
			control(obj instanceof Variable); // for the moment, only managed for a variable in this case
			int[] t = ((ConditionIntset) condition).t;
			return extension((Variable) obj, t, ((ConditionIntset) condition).operator == TypeConditionOperatorSet.IN);
		}
		if (condition instanceof ConditionIntvl) {
			Range r = (Range) condition.rightTerm();
			return intension(api.and(api.ge(obj, r.start), api.lt(obj, r.stop)));
		}
		return unimplemented("with  " + condition);
	}

	@Override
	public final CtrAlone element(Var[] list, int startIndex, Var index, TypeRank rank, Condition condition) {
		unimplementedIf(startIndex != 0 || (rank != null && rank != TypeRank.ANY), "element");
		Domain idom = ((Variable) index).dom;
		// first, we discard some possibly useless variables from list
		if (!idom.initiallyExactly(api.range(0, list.length))) {
			List<Variable> tmp = new ArrayList<>();
			for (int a = idom.first(); a != -1; a = idom.next(a)) {
				int va = idom.toVal(a);
				if (0 <= va && va < list.length)
					tmp.add((Variable) list[va]);
				else
					return (CtrAlone) unimplemented("element with an index (variable) with a bad value " + va + " " + index);
			}
			list = tmp.stream().toArray(Var[]::new);
		}
		// second, we deal with the classical uses of Element (operator EQ, and right term a value or a variable
		if (condition instanceof ConditionRel && ((ConditionRel) condition).operator == EQ) {
			if (condition instanceof ConditionVal)
				return element(list, index, safeInt(((ConditionVal) condition).k));
			return element(list, index, (Var) ((ConditionVar) condition).x);
		}
		// third, we introduce an auxiliary variable for dealing with the other cases
		int min = Stream.of(list).mapToInt(x -> ((Variable) x).dom.firstValue()).min().getAsInt();
		int max = Stream.of(list).mapToInt(x -> ((Variable) x).dom.lastValue()).max().getAsInt();
		Var aux = auxVar(new Range(min, max + 1));
		postExprSubjectToCondition(aux, condition);
		return element(list, index, aux);
	}

	/**
	 * Builds a binary extension constraint because the vector is an array of integer values (and not variables).
	 */
	private CtrEntity element(int[] list, int startIndex, Var index, TypeConditionOperatorRel op, Var value) {
		List<int[]> l = new ArrayList<>();
		Domain dx = ((Variable) index).dom, dz = ((Variable) value).dom;
		for (int a = dx.first(); a != -1; a = dx.next(a)) {
			int va = dx.toVal(a) - startIndex;
			if (0 <= va && va < list.length) { // if valid value index a in dx
				int v = list[va];
				if (op == EQ) {
					if (dz.containsValue(v))
						l.add(new int[] { va + startIndex, v });
				} else {
					for (int b = dz.first(); b != -1; b = dz.next(b)) {
						int vb = dz.toVal(b);
						boolean valid = op == LT ? v < vb : op == LE ? v <= vb : op == GE ? v >= vb : op == GT ? v > vb : v != vb;
						if (valid)
							l.add(new int[] { va + startIndex, vb });
					}
				}
			}
		}
		int[][] table = org.xcsp.common.structures.Table.clean(l);
		return extension(vars(index, value), table, true);
	}

	@Override
	public final CtrEntity element(int[] list, int startIndex, Var index, TypeRank rank, Condition condition) {
		unimplementedIf(rank != null && rank != TypeRank.ANY, "element");
		if (condition instanceof ConditionVar) // && ((ConditionRel) condition).operator == EQ)
			return element(list, startIndex, index, ((ConditionRel) condition).operator, (Var) condition.rightTerm());
		return unimplemented("element: " + startIndex + " " + condition);
	}

	private CtrEntity element(int[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, Var value) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		List<int[]> tuples = new ArrayList<>();
		Domain dx = ((Variable) rowIndex).dom, dy = ((Variable) colIndex).dom, dz = ((Variable) value).dom;
		for (int a = dx.first(); a != -1; a = dx.next(a))
			for (int b = dy.first(); b != -1; b = dy.next(b)) {
				int i = dx.toVal(a), j = dy.toVal(b);
				if (0 <= i && i < matrix.length && 0 <= j && j < matrix[i].length && dz.containsValue(matrix[i][j]))
					tuples.add(new int[] { i, j, matrix[i][j] });
			}
		return extension(vars(rowIndex, colIndex, value), org.xcsp.common.structures.Table.clean(tuples), true);
	}

	@Override
	public CtrEntity element(int[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, Condition condition) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		if (condition instanceof ConditionVar && ((ConditionRel) condition).operator == EQ)
			return element(matrix, startRowIndex, rowIndex, startColIndex, colIndex, (Var) condition.rightTerm());
		int[] values = Stream.of(matrix).flatMapToInt(t -> IntStream.of(t)).distinct().sorted().toArray();
		Var aux = auxVar(values);
		postExprSubjectToCondition(aux, condition);
		return element(matrix, startRowIndex, rowIndex, startColIndex, colIndex, aux);
	}

	private CtrEntity element(Var[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, int value) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		if (rowIndex == colIndex) {
			control(matrix.length == matrix[0].length);
			Var[] t = IntStream.range(0, matrix.length).mapToObj(i -> matrix[i][i]).toArray(Var[]::new);
			return element(t, rowIndex, value);
		}
		return post(new ElementMatrixCst(this, (Variable[][]) matrix, (Variable) rowIndex, (Variable) colIndex, value));
	}

	private CtrEntity element(Var[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, Var value) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		if (rowIndex == colIndex) {
			control(matrix.length == matrix[0].length);
			Var[] t = IntStream.range(0, matrix.length).mapToObj(i -> matrix[i][i]).toArray(Var[]::new);
			return element(t, rowIndex, value);
		}
		return post(new ElementMatrixVar(this, (Variable[][]) matrix, (Variable) rowIndex, (Variable) colIndex, (Variable) value));
	}

	public CtrEntity element(Var[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, Condition condition) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		if (condition instanceof ConditionVal && ((ConditionRel) condition).operator == EQ)
			return element(matrix, startRowIndex, rowIndex, startColIndex, colIndex, safeInt(((ConditionVal) condition).k));
		if (condition instanceof ConditionVar && ((ConditionRel) condition).operator == EQ)
			return element(matrix, startRowIndex, rowIndex, startColIndex, colIndex, (Var) ((ConditionVar) condition).x);
		return unimplemented("element");
	}

	// ************************************************************************
	// ***** Constraint channel
	// ************************************************************************

	@Override
	public CtrEntity channel(Var[] list, int startIndex) {
		unimplementedIf(startIndex != 0, "channel");
		allDifferent(list); // TODO additional constraint; controlling the fact of posting it?
		return forall(range(list.length), i -> element(list, list[i], i));
	}

	@Override
	public CtrEntity channel(Var[] list1, int startIndex1, Var[] list2, int startIndex2) {
		control(Stream.of(list1).noneMatch(x -> x == null) && Stream.of(list2).noneMatch(x -> x == null));
		control(startIndex1 == 0 && startIndex2 == 0, "unimplemented case for channel");
		if (list1.length == list2.length) { // TODO additional constraints; controlling the fact of posting them?
			allDifferent(list1);
			allDifferent(list2);
		}
		return forall(range(list1.length), i -> element(list2, list1[i], i));
	}

	@Override
	public final CtrEntity channel(Var[] list, int startIndex, Var value) {
		control(Stream.of(list).noneMatch(x -> x == null) && startIndex == 0);
		control(Variable.areAllInitiallyBoolean((Variable[]) list) && ((Variable) value).dom.initiallyExactly(range(list.length)));
		// exactly((VariableInteger[]) list, 1, 1); // TODO what would be the benefit of posting it?
		return forall(range(list.length), i -> post(new Reif2EQ(this, (Variable) list[i], (Variable) value, i)));
		// intension(iff(list[i], eq(value, i))));
	}

	// ************************************************************************
	// ***** Constraint stretch
	// ************************************************************************

	@Override
	public CtrEntity stretch(Var[] list, int[] values, int[] widthsMin, int[] widthsMax, int[][] patterns) {
		control(values.length == widthsMin.length && values.length == widthsMax.length);
		control(IntStream.range(0, values.length).allMatch(i -> widthsMin[i] <= widthsMax[i]));
		control(patterns == null || Stream.of(patterns).allMatch(t -> t.length == 2));
		return unimplemented("stretch");
	}

	// ************************************************************************
	// ***** Constraint noOverlap
	// ************************************************************************

	/**
	 * 1-dimensional no-overlap
	 * 
	 * About redundant constraints:
	 * 
	 * a) posting allDifferent(origins) really seems uninteresting (too weak)
	 * 
	 * b) posting cumulative(origins, lengths, null, Kit.repeat(1, origins.length), api.condition(LE, 1)) does not seem
	 * to be very interesting. To be checked!
	 */
	@Override
	public final CtrEntity noOverlap(Var[] origins, int[] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		if (origins.length >= 10 && head.control.global.redundNoOverlap) { // TODO hard coding 10
			// we post redundant constraints (after introducing auxiliary variables)
			Var[] aux = auxVarArray(origins.length, range(origins.length));
			allDifferent(aux);
			for (int i = 0; i < origins.length; i++)
				for (int j = i + 1; j < origins.length; j++)
					intension(iff(le(aux[i], aux[j]), le(origins[i], origins[j])));
		}
		for (int i = 0; i < origins.length; i++)
			for (int j = i + 1; j < origins.length; j++) {
				Variable xi = (Variable) origins[i], xj = (Variable) origins[j];
				int li = lengths[i], lj = lengths[j];
				if (xi.dom.lastValue() + li <= xj.dom.firstValue() || xj.dom.lastValue() + lj <= xi.dom.firstValue())
					continue;
				if (head.control.global.noOverlap == INTENSION_DECOMPOSITION)
					intension(or(le(add(xi, li), xj), le(add(xj, lj), xi)));
				else if (head.control.global.noOverlap == EXTENSION_HYBRID)
					post(CHybrid.noOverlap(this, xi, xj, li, lj));
				else
					post(new Disjonctive(this, xi, li, xj, lj)); // BASE
			}
		return null;
	}

	@Override
	public final CtrEntity noOverlap(Var[] origins, Var[] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		for (int i = 0; i < origins.length; i++)
			for (int j = i + 1; j < origins.length; j++) {
				Variable xi = (Variable) origins[i], xj = (Variable) origins[j];
				Variable wi = (Variable) lengths[i], wj = (Variable) lengths[j];
				if (head.control.global.noOverlap == INTENSION_DECOMPOSITION)
					intension(or(le(add(xi, wi), xj), le(add(xj, wj), xi)));
				else
					post(new DisjonctiveVar(this, xi, xj, wi, wj));
			}
		return null;
	}

	@Override
	public final CtrEntity noOverlap(Var[][] origins, int[][] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		unimplementedIf(origins[0].length != 2, "noOverlap " + Utilities.join(origins));
		if (head.control.global.redundNoOverlap) {
			// we post two redundant cumulative constraints, and a global noOverlap
			// TODO post only if pressure is high (related to number of continues below)
			Var[] ox = Stream.of(origins).map(t -> t[0]).toArray(Var[]::new), oy = Stream.of(origins).map(t -> t[1]).toArray(Var[]::new);
			int[] tx = Stream.of(lengths).mapToInt(t -> t[0]).toArray(), ty = Stream.of(lengths).mapToInt(t -> t[1]).toArray();
			int minX = Stream.of(ox).mapToInt(x -> ((Variable) x).dom.firstValue()).min().orElseThrow();
			int maxX = IntStream.range(0, ox.length).map(i -> ((Variable) ox[i]).dom.lastValue() + tx[i]).max().orElseThrow();
			int minY = Stream.of(oy).mapToInt(x -> ((Variable) x).dom.firstValue()).min().orElseThrow();
			int maxY = IntStream.range(0, oy.length).map(i -> ((Variable) oy[i]).dom.lastValue() + ty[i]).max().orElseThrow();
			cumulative(ox, tx, null, ty, api.condition(LE, maxY - (long) minY));
			cumulative(oy, ty, null, tx, api.condition(LE, maxX - (long) minX));
			post(new NoOverlap(this, translate(ox), tx, translate(oy), ty)); // TODO: may be very expensive
		}

		for (int i = 0; i < origins.length; i++)
			for (int j = i + 1; j < origins.length; j++) {
				Variable xi = (Variable) origins[i][0], xj = (Variable) origins[j][0], yi = (Variable) origins[i][1], yj = (Variable) origins[j][1];
				int wi = lengths[i][0], wj = lengths[j][0], hi = lengths[i][1], hj = lengths[j][1];
				if (xi.dom.lastValue() + wi <= xj.dom.firstValue() || xj.dom.lastValue() + wj <= xi.dom.firstValue())
					continue;
				if (yi.dom.lastValue() + hi <= yj.dom.firstValue() || yj.dom.lastValue() + hj <= yi.dom.firstValue())
					continue;
				if (head.control.global.noOverlap == INTENSION_DECOMPOSITION) // VERY expensive
					intension(or(le(add(xi, wi), xj), le(add(xj, wj), xi), le(add(yi, hi), yj), le(add(yj, hj), yi)));
				else if (head.control.global.noOverlap == EXTENSION_STARRED) // seems to be rather efficient
					extension(vars(xi, xj, yi, yj), Table.starredNoOverlap(xi, xj, yi, yj, wi, wj, hi, hj), true, true);
				else if (head.control.global.noOverlap == EXTENSION_HYBRID)
					post(CHybrid.noOverlap(this, xi, yi, xj, yj, wi, hi, wj, hj));
				else
					post(new Disjonctive2D(this, xi, xj, yi, yj, wi, wj, hi, hj));
			}
		return null;
	}

	@Override
	public final CtrEntity noOverlap(Var[][] origins, Var[][] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		for (int i = 0; i < origins.length; i++)
			for (int j = i + 1; j < origins.length; j++) {
				Variable xi = (Variable) origins[i][0], xj = (Variable) origins[j][0], yi = (Variable) origins[i][1], yj = (Variable) origins[j][1];
				Variable wi = (Variable) lengths[i][0], wj = (Variable) lengths[j][0], hi = (Variable) lengths[i][1], hj = (Variable) lengths[j][1];
				if (head.control.global.noOverlap == EXTENSION_HYBRID && Stream.of(wi, wj, hi, hj).allMatch(x -> x.dom.initSize() == 2))
					post(CHybrid.noOverlap(this, xi, yi, xj, yj, wi, hi, wj, hj));
				else
					intension(or(le(add(xi, wi), xj), le(add(xj, wj), xi), le(add(yi, hi), yj), le(add(yj, hj), yi)));
			}
		return null;
	}

	public final CtrEntity noOverlap(Var[] xs, Var[] ys, Var[] lx, int[] ly, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		for (int i = 0; i < xs.length; i++)
			for (int j = i + 1; j < xs.length; j++) {
				Variable xi = (Variable) xs[i], xj = (Variable) xs[j], yi = (Variable) ys[i], yj = (Variable) ys[j];
				Variable wi = (Variable) lx[i], wj = (Variable) lx[j];
				int hi = ly[i], hj = ly[j];
				intension(or(le(add(xi, wi), xj), le(add(xj, wj), xi), le(add(yi, hi), yj), le(add(yj, hj), yi)));
			}
		return null;
	}

	// ************************************************************************
	// ***** Constraint Cumulative
	// ************************************************************************

	@Override
	public final CtrEntity cumulative(Var[] origins, int[] lengths, Var[] ends, int[] heights, Condition condition) {
		unimplementedIf(ends != null, "cumulative");
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op == LT || op == LE);
			int limit = Utilities.safeInt(((ConditionVal) condition).k);
			if (origins.length == 1) {
				if (heights[0] == 0 || heights[0] <= limit - (op == LT ? 1 : 0))
					return null; // discarded constraint because initially entailed // return CtrTrue ?
				return post(new CtrFalse(this, translate(origins), "Unary Cumulative"));
			}
			return post(new CumulativeCst(this, translate(origins), lengths, heights, op == LT ? limit - 1 : limit));
		}
		if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			control(op == LE);
			Variable limit = (Variable) (((ConditionVar) condition).x);
			return post(new CumulativeVarC(this, translate(origins), lengths, heights, limit));
		}
		return unimplemented("cumulative");
	}

	@Override
	public final CtrEntity cumulative(Var[] origins, Var[] lengths, Var[] ends, int[] heights, Condition condition) {
		unimplementedIf(ends != null, "cumulative");
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op == LT || op == LE);
			int limit = Utilities.safeInt(((ConditionVal) condition).k);
			return post(new CumulativeVarW(this, translate(origins), translate(lengths), heights, op == LT ? limit - 1 : limit));
		}
		if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			control(op == LE);
			Variable limit = (Variable) (((ConditionVar) condition).x);
			return post(new CumulativeVarWC(this, translate(origins), translate(lengths), heights, limit));
		}
		return unimplemented("cumulative");
	}

	@Override
	public final CtrEntity cumulative(Var[] origins, int[] lengths, Var[] ends, Var[] heights, Condition condition) {
		unimplementedIf(ends != null, "cumulative");
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op == LT || op == LE);
			int limit = Utilities.safeInt(((ConditionVal) condition).k);
			return post(new CumulativeVarH(this, translate(origins), lengths, translate(heights), op == LT ? limit - 1 : limit));
		}
		if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			control(op == LE);
			Variable limit = (Variable) (((ConditionVar) condition).x);
			return post(new CumulativeVarHC(this, translate(origins), lengths, translate(heights), limit));
		}
		return unimplemented("cumulative");
	}

	@Override
	public final CtrEntity cumulative(Var[] origins, Var[] lengths, Var[] ends, Var[] heights, Condition condition) {
		unimplementedIf(ends != null, "cumulative");
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op == LT || op == LE);
			int limit = Utilities.safeInt(((ConditionVal) condition).k);
			return post(new CumulativeVarWH(this, translate(origins), translate(lengths), translate(heights), op == LT ? limit - 1 : limit));
		}
		if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			control(op == LE);
			Variable limit = (Variable) (((ConditionVar) condition).x);
			return post(new CumulativeVarWHC(this, translate(origins), translate(lengths), translate(heights), limit));
		}
		return unimplemented("cumulative");
	}

	// ************************************************************************
	// ***** Constraint BinPacking
	// ************************************************************************

	public final CtrEntity binpacking(Var[] list, int[] sizes, Condition condition) {
		control(list.length > 2 && list.length == sizes.length);
		Variable[] vars = translate(list);
		boolean sameType = Variable.haveSameDomainType(vars);
		if (!sameType || head.control.global.binpacking == 1) { // decomposing in sum constraints
			int[] bins = Variable.setOfvaluesIn(vars).stream().mapToInt(v -> v).sorted().toArray();
			return forall(range(bins.length), i -> sum(Stream.of(list).map(x -> api.eq(x, bins[i])), sizes, condition));
			// TODO add nValues ? other ?
		}
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op == LT || op == LE);
			int limit = Utilities.safeInt(((ConditionVal) condition).k);
			// return post(new BinPackingSimple(this, vars, sizes, limit - (op == LT ? 1 : 0)));
			return post(new BinPackingEnergetic(this, vars, sizes, limit - (op == LT ? 1 : 0)));
			// TODO add nValues ? other ?
		}
		return unimplemented("binPacking");
	}

	public final CtrEntity binpacking(Var[] list, int[] sizes, int[] capacities, boolean loads) {
		control(list.length > 2 && list.length == sizes.length);
		TypeConditionOperatorRel op = loads ? EQ : LE;
		Variable[] vars = translate(list);
		boolean sameType = Variable.haveSameDomainType(vars);
		if (loads || !sameType || head.control.global.binpacking == 1) { // decomposing in sum constraints
			int[] bins = Variable.setOfvaluesIn(vars).stream().mapToInt(v -> v).sorted().toArray();
			control(0 <= bins[0] && bins[bins.length - 1] < capacities.length);
			return forall(range(bins.length), i -> sum(Stream.of(list).map(x -> api.eq(x, bins[i])), sizes, Condition.buildFrom(op, capacities[bins[i]])));
		}
		return post(new BinPackingEnergetic(this, vars, sizes, capacities)); // TODO add nValues ? other ?
	}

	public final CtrEntity binpacking(Var[] list, int[] sizes, Var[] capacities, boolean loads) {
		control(list.length > 2 && list.length == sizes.length);
		TypeConditionOperatorRel op = loads ? EQ : LE;
		Variable[] vars = translate(list);
		boolean sameType = Variable.haveSameDomainType(vars);
		if (!loads || !sameType || head.control.global.binpacking == 1) { // decomposing in sum constraints
			int[] bins = Variable.setOfvaluesIn(vars).stream().mapToInt(v -> v).sorted().toArray();
			control(0 <= bins[0] && bins[bins.length - 1] < capacities.length);
			return forall(range(bins.length), i -> sum(Stream.of(list).map(x -> api.eq(x, bins[i])), sizes, Condition.buildFrom(op, capacities[bins[i]])));
		}
		return post(new BinPackingEnergeticLoad(this, vars, sizes, translate(capacities))); // TODO add nValues ? other
																							// ?
	}

	public final CtrEntity binpacking(Var[] list, int[] sizes, Condition[] conditions, int startIndex) {
		control(list.length > 2 && list.length == sizes.length);
		control(Stream.of(conditions).allMatch(c -> c instanceof ConditionVar && ((ConditionVar) c).operator == EQ));
		Variable[] vars = translate(list);
		boolean sameType = Variable.haveSameDomainType(vars);
		if (!sameType || head.control.global.binpacking == 1) { // decomposing in sum constraints
			int[] bins = Variable.setOfvaluesIn(vars).stream().mapToInt(v -> v).sorted().toArray();
			control(bins.length == conditions.length);
			return forall(range(bins.length), i -> sum(Stream.of(list).map(x -> api.eq(x, bins[i])), sizes, conditions[i]));
			// TODO add nValues ? other ?
		}
		if (Stream.of(conditions).allMatch(c -> c instanceof ConditionVar && ((ConditionVar) c).operator == EQ)) {
			Variable[] loads = Stream.of(conditions).map(c -> ((ConditionVar) c).x).toArray(Variable[]::new);
			return post(new BinPackingEnergeticLoad(this, vars, sizes, loads));
		}
		return unimplemented("binPacking");
	}

	// ************************************************************************
	// ***** Constraints Knapsack and Flow
	// ************************************************************************

	public final CtrEntity knapsack(Var[] list, int[] weights, Condition wcondition, int[] profits, Condition pcondition) {
		// for the moment, no dedicated propagator (just decomposition)
		sum(list, weights, wcondition);
		return sum(list, profits, pcondition);
	}

	public final CtrEntity flow(Var[] list, int[] balance, int[][] arcs) {
		// for the moment, no dedicated propagator (just decomposition)
		int[] nodes = IntStream.range(0, arcs.length).flatMap(t -> IntStream.of(arcs[t])).distinct().sorted().toArray();
		control(nodes.length == balance.length);
		int sm = nodes[0];
		List<Var>[] preds = (List<Var>[]) IntStream.range(0, nodes.length).mapToObj(i -> new ArrayList<>()).toArray(List<?>[]::new);
		List<Var>[] succs = (List<Var>[]) IntStream.range(0, nodes.length).mapToObj(i -> new ArrayList<>()).toArray(List<?>[]::new);
		for (int i = 0; i < arcs.length; i++) {
			preds[arcs[i][1] - sm].add(list[i]);
			succs[arcs[i][0] - sm].add(list[i]);
		}
		for (int i = 0; i < nodes.length; i++) {
			List<Var> s = succs[i], p = preds[i];
			int[] coeffs = IntStream.range(0, s.size() + p.size()).map(j -> j < s.size() ? 1 : -1).toArray();
			sum((Var[]) vars(succs[i], preds[i]), coeffs, Condition.buildFrom(EQ, balance[i]));
		}
		return null;
	}

	public final CtrEntity flow(Var[] list, int[] balance, int[][] arcs, int[] weights, Condition condition) {
		// for the moment, no dedicated propagator (just decomposition)
		flow(list, balance, arcs);
		return sum(list, weights, condition);
	}

	// ************************************************************************
	// ***** Constraint circuit
	// ************************************************************************

	@Override
	public CtrEntity circuit(Var[] list, int startIndex) {
		unimplementedIf(startIndex != 0, "circuit");
		Variable[] vars = translate(list);
		return post(head.control.global.circuit == 0 ? new Circuit(this, vars) : new Circuit2(this, vars));
	}

	@Override
	public CtrEntity circuit(Var[] list, int startIndex, int size) {
		unimplementedIf(startIndex != 0, "circuit");
		api.sum(IntStream.range(0, list.length).mapToObj(i -> api.ne(list[i], i)), null, api.condition(EQ, size));
		return circuit(list, startIndex);
	}

	@Override
	public CtrEntity circuit(Var[] list, int startIndex, Var size) {
		unimplementedIf(startIndex != 0, "circuit");
		api.sum(IntStream.range(0, list.length).mapToObj(i -> api.ne(list[i], i)), null, api.condition(EQ, size));
		return circuit(list, startIndex);
	}

	// ************************************************************************
	// ***** Constraint clause
	// ************************************************************************

	@Override
	public final CtrEntity clause(Var[] list, Boolean[] phases) {
		control(Stream.of(list).noneMatch(x -> x == null), "A variable in array list is null");
		control(list.length == phases.length, "Bad form of clause");
		control(Variable.areAllInitiallyBoolean((Variable[]) list), "A variable is not Boolean in the array list.");
		return sum(list, Stream.of(phases).mapToInt(p -> p ? 1 : -1).toArray(), api.condition(NE, -Stream.of(phases).filter(p -> !p).count()));
	}

	public final CtrEntity clause(Var[] pos, Var[] neg) {
		control(Stream.of(pos).noneMatch(x -> x == null) && Stream.of(neg).noneMatch(x -> x == null), "No null values is allowed in the specified arrays.");
		Boolean[] phases = IntStream.range(0, pos.length + neg.length).mapToObj(i -> (Boolean) (i < pos.length)).toArray(Boolean[]::new);
		return clause(vars(pos, (Object) neg), phases);
	}

	// ************************************************************************
	// ***** Constraints instantiation and refutation
	// ************************************************************************

	@Override
	public final CtrEntity instantiation(Var[] list, int[] values) {
		control(list.length == values.length && list.length > 0, list.length + " vs " + values.length);
		return forall(range(list.length), i -> equal(list[i], values[i]));
	}

	public final CtrEntity instantiation(Var[] list, int value) {
		return instantiation(list, Kit.repeat(value, list.length));
	}

	public final CtrEntity refutation(Var[] list, int[] values) {
		control(list.length == values.length && list.length > 0);
		return forall(range(list.length), i -> different(list[i], values[i]));
	}

	public final CtrEntity refutation(Var[] list, int value) {
		return refutation(list, Kit.repeat(value, list.length));
	}

	// ************************************************************************
	// ***** Meta-Constraint slide, ifThen and ifThenElse
	// ************************************************************************

	@Override
	public final CtrEntity slide(IVar[] list, Range range, IntFunction<CtrEntity> template) {
		control(range.start == 0 && range.length() > 0);
		if (range.length() == 1)
			return template.apply(0);
		return manageLoop(() -> IntStream.range(0, range.stop).filter(i -> i % range.step == 0).mapToObj(i -> (Constraint) ((CtrAlone) template.apply(i)).ctr)
				.toArray(Constraint[]::new));
	}

	@Override
	public final CtrEntity ifThen(CtrEntity c1, CtrEntity c2) {
		return unimplemented("ifthen");
	}

	@Override
	public final CtrEntity ifThenElse(CtrEntity c1, CtrEntity c2, CtrEntity c3) {
		return unimplemented("ifthenElse");
	}

	// ************************************************************************
	// ***** Constraint smart
	// ************************************************************************

	/** Builds and returns a smart constraint. */
	public final CtrAlone hybrid(IVar[] scp, HybridTuple... smartTuples) {
		return post(new CHybrid(this, translate(scp), smartTuples));
	}

	public final CtrAlone hybrid(IVar[] scp, Stream<HybridTuple> smartTuples) {
		return post(new CHybrid(this, translate(scp), smartTuples));
	}

	/**********************************************************************************************
	 *** Posting Objectives
	 *********************************************************************************************/

	/**
	 * Posts the specified objective (constraint), i.e., records it as being the objective of the problem
	 * 
	 * @param c
	 *            an objective constraint to be posted
	 * @return the posted objective
	 */
	public final Optimizable postObj(Constraint c) {
		c.num = features.collecting.add(c);
		return (Optimizable) c;
	}

	private Optimizer buildOptimizer(TypeOptimization opt, Optimizable clb, Optimizable cub) {
		control(optimizer == null, "Only mono-objective currently supported");
		if (head.control.optimization.strategy == OptimizationStrategy.DECREASING)
			return new OptimizerDecreasing(this, opt, clb, cub);
		if (head.control.optimization.strategy == OptimizationStrategy.INCREASING)
			return new OptimizerIncreasing(this, opt, clb, cub);
		control(head.control.optimization.strategy == OptimizationStrategy.DICHOTOMIC);
		return new OptimizerDichotomic(this, opt, clb, cub);
		// the code below must be changed, as for heuristics, if we want to use it, see in Head, HandlerClasses
		// return Reflector.buildObject(suffix, Optimizer.class, this, opt, c);
	}

	private boolean switchToSatisfaction(TypeOptimization opt, TypeObjective obj, int[] coeffs, Variable... list) {
		int limit = options.satisfactionLimit;
		if (limit == PLUS_INFINITY_INT)
			return false;
		if (obj == EXPRESSION) {
			control(list.length == 1 && coeffs == null);
			intension(opt == MINIMIZE ? le(list[0], limit) : ge(list[0], limit));
		} else if (coeffs != null) {
			control(obj == SUM);
			sum(list, coeffs, opt == MINIMIZE ? LE : GE, limit);
		} else {
			control(obj.generalizable());
			if (opt == MINIMIZE) {
				if (obj == SUM)
					post(new SumSimpleLE(this, list, limit));
				else if (obj == MINIMUM)
					post(new MinimumCstLE(this, list, limit));
				else if (obj == MAXIMUM)
					forall(range(list.length), i -> lessEqual(list[i], limit));
				else
					post(new NValuesCstLE(this, list, limit));
			} else {
				if (obj == SUM)
					post(new SumSimpleGE(this, list, limit));
				else if (obj == MINIMUM)
					forall(range(list.length), i -> greaterEqual(list[i], limit));
				else if (obj == MAXIMUM)
					post(new MaximumCstGE(this, list, limit));
				else
					post(new NValuesCstGE(this, list, limit));
			}
		}
		return true;
	}

	private ObjEntity optimize(TypeOptimization opt, IVar x) {
		if (!switchToSatisfaction(opt, EXPRESSION, null, (Variable) x)) {
			long lb = head.control.optimization.lb, ub = head.control.optimization.ub;
			optimizer = buildOptimizer(opt, postObj(new ObjVarGE(this, (Variable) x, lb)), postObj(new ObjVarLE(this, (Variable) x, ub)));
		}
		return null;
	}

	@Override
	public final ObjEntity minimize(IVar x) {
		return optimize(MINIMIZE, x);
	}

	@Override
	public final ObjEntity maximize(IVar x) {
		return optimize(MAXIMIZE, x);
	}

	private final ObjEntity optimize(TypeOptimization opt, XNode<IVar> tree) {
		return optimize(opt, replaceByVariable(tree));
	}

	@Override
	public final ObjEntity minimize(XNode<IVar> tree) {
		return optimize(MINIMIZE, tree);
	}

	@Override
	public final ObjEntity maximize(XNode<IVar> tree) {
		return optimize(MAXIMIZE, tree);
	}

	private ObjEntity optimize(TypeOptimization opt, TypeObjective type, Variable[] list) {
		control(type.generalizable() && list.length > 0);
		if (!switchToSatisfaction(opt, type, null, list)) {
			if (list.length == 1) {
				control(type != NVALUES);
				return optimize(opt, list[0]);
			}
			long lb = head.control.optimization.lb, ub = head.control.optimization.ub;
			// TODO what about several occurrences of the same variable in list?0
			// if SUM, should we transform into weighted sum, or just fail?
			Constraint clb = type == SUM ? new SumSimpleGE(this, list, lb)
					: type == MINIMUM ? new MinimumCstGE(this, list, lb)
							: type == MAXIMUM ? new MaximumCstGE(this, list, lb) : new NValuesCstGE(this, list, lb);
			Constraint cub = type == SUM ? new SumSimpleLE(this, list, ub)
					: type == MINIMUM ? new MinimumCstLE(this, list, ub)
							: type == MAXIMUM ? new MaximumCstLE(this, list, ub) : new NValuesCstLE(this, list, ub);
			optimizer = buildOptimizer(opt, postObj(clb), postObj(cub));
		}
		return null;
	}

	@Override
	public final ObjEntity minimize(TypeObjective type, IVar[] list) {
		return optimize(MINIMIZE, type, translate(list));
	}

	@Override
	public final ObjEntity maximize(TypeObjective type, IVar[] list) {
		return optimize(MAXIMIZE, type, translate(list));
	}

	private ObjEntity optimize(TypeOptimization opt, TypeObjective type, Variable[] list, int[] coeffs) {
		control(type == SUM && coeffs != null && list.length == coeffs.length && list.length > 0);
		if (!switchToSatisfaction(opt, type, coeffs, list)) {
			if (list.length == 1)
				return optimize(opt, mul(list[0], coeffs[0]));
			long lb = head.control.optimization.lb, ub = head.control.optimization.ub;
			optimizer = buildOptimizer(opt, (Optimizable) ((CtrAlone) sum(list, coeffs, GE, lb, false)).ctr,
					(Optimizable) ((CtrAlone) sum(list, coeffs, LE, ub, false)).ctr);
		}
		return null;
	}

	@Override
	public final ObjEntity minimize(TypeObjective type, IVar[] list, int[] coeffs) {
		return optimize(MINIMIZE, type, translate(list), coeffs);
	}

	@Override
	public final ObjEntity maximize(TypeObjective type, IVar[] list, int[] coeffs) {
		return optimize(MAXIMIZE, type, translate(list), coeffs);
	}

	private ObjEntity optimize(TypeOptimization opt, TypeObjective type, XNode<IVar>[] trees) {
		control(type != EXPRESSION && type != LEX && trees.length > 0);
		if (trees.length == 1) {
			control(type != NVALUES);
			return optimize(opt, trees[0]);
		}
		return optimize(opt, type, translate(replaceByVariables(trees)));
	}

	@Override
	public ObjEntity minimize(TypeObjective type, XNode<IVar>[] trees) {
		return optimize(MINIMIZE, type, trees);
	}

	@Override
	public ObjEntity maximize(TypeObjective type, XNode<IVar>[] trees) {
		return optimize(MAXIMIZE, type, trees);
	}

	private ObjEntity optimize(TypeOptimization opt, TypeObjective type, XNode<IVar>[] trees, int[] coeffs) {
		control(type != EXPRESSION && type != LEX && trees.length == coeffs.length && trees.length > 0);
		if (IntStream.of(coeffs).anyMatch(c -> c == 0)) // we discard useless terms, if any is present
			return optimize(opt, type, IntStream.range(0, trees.length).filter(i -> coeffs[i] != 0).mapToObj(i -> trees[i]).toArray(XNode[]::new),
					IntStream.range(0, trees.length).filter(i -> coeffs[i] != 0).map(i -> coeffs[i]).toArray());
		if (type == SUM && trees.length > 1)
			return optimize(opt, type, translate(replaceByVariables(trees)), coeffs);
		if (trees.length == 1) {
			control(type != NVALUES);
			return optimize(opt, mul(trees[0], coeffs[0]));
		}
		return optimize(opt, type, translate(replaceByVariables(IntStream.range(0, trees.length).mapToObj(i -> mul(trees[i], coeffs[i])))));
	}

	@Override
	public ObjEntity minimize(TypeObjective type, XNode<IVar>[] trees, int[] coeffs) {
		return optimize(MINIMIZE, type, trees, coeffs);
	}

	@Override
	public ObjEntity maximize(TypeObjective type, XNode<IVar>[] trees, int[] coeffs) {
		return optimize(MAXIMIZE, type, trees, coeffs);
	}

	/**********************************************************************************************
	 * Managing Annotations
	 *********************************************************************************************/

	@Override
	public void decisionVariables(IVar[] list) {
		if (options.enableAnnotations)
			super.decisionVariables(list);
	}

}

// public final Constraint addUniversalConstraintDynamicallyBetween(Variable x, Variable y) {
// assert x.getClass() == y.getClass();
// assert !Stream.of(y.ctrs).anyMatch(c -> c.scp.length == 2 && c.involves(x));
// assert solver.propagation instanceof Forward;
//
// CtrAlone ca = extension(vars(x, y), new int[0][], false, DONT_KNOW);
// Constraint c = (Constraint) ca.ctr; // (Constraint) buildCtrTrue(x, y).ctr;
// c.cloneStructures(false);
// constraints = features.collecting.constraints.toArray(new Constraint[0]); // storeConstraintsToArray();
// x.whenFinishedProblemConstruction();
// y.whenFinishedProblemConstruction();
// // constraint.buildBitRmResidues();
// if (x.assigned())
// c.doPastVariable(x);
// if (y.assigned())
// c.doPastVariable(y);
// return c;
// }

/// **
// *
// * /** Removes a constraint that has already been built. Should not be called when modeling. Advanced use.
// */
// public void removeCtr(Constraint c) {
// // System.out.println("removed " + c + "size=" + stuff.collectedCtrsAtInit.size());
// control(constraints == null, "too late");
// features.collectedCtrsAtInit.remove(c);
// // maybe was not present
// Stream.of(c.scp).forEach(x -> x.collectedCtrs.remove(c));
// // TODO other things to do ??
// CtrAlone ca = ctrEntities.ctrToCtrAlone.get(c); // remove(c);
// ctrEntities.allEntities.remove(ca);
// ctrEntities.ctrToCtrAlone.remove(c);
// }