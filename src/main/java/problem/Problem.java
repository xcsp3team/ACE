package problem;

import static java.util.stream.Collectors.groupingBy;
import static java.util.stream.Collectors.summingLong;
import static org.xcsp.common.Constants.ALL;
import static org.xcsp.common.Constants.PLUS_INFINITY_INT;
import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.NE;
import static org.xcsp.common.Types.TypeExpr.LONG;
import static org.xcsp.common.Types.TypeExpr.VAR;
import static org.xcsp.common.Types.TypeFramework.COP;
import static org.xcsp.common.Types.TypeObjective.EXPRESSION;
import static org.xcsp.common.Types.TypeObjective.MAXIMUM;
import static org.xcsp.common.Types.TypeObjective.MINIMUM;
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
import static org.xcsp.common.predicates.MatcherInterface.val;
import static org.xcsp.common.predicates.MatcherInterface.var;
import static org.xcsp.common.predicates.MatcherInterface.varOrVal;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.ariop;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.relop;
import static org.xcsp.common.predicates.MatcherInterface.AbstractOperation.unalop;
import static org.xcsp.common.predicates.XNode.node;
import static org.xcsp.common.predicates.XNodeParent.add;
import static org.xcsp.common.predicates.XNodeParent.eq;
import static org.xcsp.common.predicates.XNodeParent.iff;
import static org.xcsp.common.predicates.XNodeParent.in;
import static org.xcsp.common.predicates.XNodeParent.le;
import static org.xcsp.common.predicates.XNodeParent.ne;
import static org.xcsp.common.predicates.XNodeParent.or;
import static utility.Kit.log;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.IntFunction;
import java.util.stream.Collectors;
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
import org.xcsp.common.enumerations.EnumerationCartesian;
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
import org.xcsp.modeler.implementation.ProblemIMP;

import constraints.ConflictsStructure;
import constraints.Constraint;
import constraints.Constraint.CtrHardFalse;
import constraints.Constraint.CtrHardTrue;
import constraints.extension.Extension;
import constraints.extension.Extension.Extension1;
import constraints.extension.ExtensionMDD;
import constraints.extension.ExtensionSmart;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableSmart.SmartTuple;
import constraints.global.AllDifferent.AllDifferentBound;
import constraints.global.AllDifferent.AllDifferentComplete;
import constraints.global.AllDifferent.AllDifferentCounting;
import constraints.global.AllDifferent.AllDifferentExceptWeak;
import constraints.global.AllDifferent.AllDifferentPermutation;
import constraints.global.AllDifferent.AllDifferentWeak;
import constraints.global.Among;
import constraints.global.Cardinality.CardinalityConstant;
import constraints.global.Circuit;
import constraints.global.Count.CountCst.AtLeast1;
import constraints.global.Count.CountCst.AtLeastK;
import constraints.global.Count.CountCst.AtMost1;
import constraints.global.Count.CountCst.AtMostK;
import constraints.global.Count.CountCst.Exactly1;
import constraints.global.Count.CountCst.ExactlyK;
import constraints.global.Count.CountVar.ExactlyVarK;
import constraints.global.Cumulative;
import constraints.global.Element.ElementConstant;
import constraints.global.Element.ElementVariable;
import constraints.global.ElementMatrix;
import constraints.global.Extremum.ExtremumCst;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstGE;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstGE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstLE;
import constraints.global.Extremum.ExtremumVar.Maximum;
import constraints.global.Extremum.ExtremumVar.Minimum;
import constraints.global.Lexicographic;
import constraints.global.NValues.NValuesCst;
import constraints.global.NValues.NValuesCst.NValuesCstGE;
import constraints.global.NValues.NValuesCst.NValuesCstLE;
import constraints.global.NValues.NValuesVar.NValuesVarEQ;
import constraints.global.NotAllEqual;
import constraints.global.Sum.SumSimple;
import constraints.global.Sum.SumSimple.SumSimpleGE;
import constraints.global.Sum.SumSimple.SumSimpleLE;
import constraints.global.Sum.SumWeighted;
import constraints.global.Sum.SumWeighted.SumWeightedGE;
import constraints.global.Sum.SumWeighted.SumWeightedLE;
import constraints.global.SumScalarBoolean.SumScalarBooleanCst;
import constraints.global.SumScalarBoolean.SumScalarBooleanVar;
import constraints.intension.Intension;
import constraints.intension.PrimitiveBinary.Disjonctive;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryEQWithUnaryOperator;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryLog;
import constraints.intension.PrimitiveBinary.PrimitiveBinarySub;
import constraints.intension.PrimitiveBinary.PrimitiveBinarySub.SubNE2;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryWithCst;
import constraints.intension.PrimitiveLogic.PrimitiveLogicEq;
import constraints.intension.PrimitiveTernary;
import constraints.intension.PrimitiveTernary.PrimitiveTernaryAdd;
import constraints.intension.PrimitiveTernary.PrimitiveTernaryLog;
import dashboard.Control.SettingGeneral;
import dashboard.Control.SettingVars;
import dashboard.Control.SettingXml;
import heuristics.HeuristicValues;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicValuesDirect.Last;
import heuristics.HeuristicValuesDirect.Values;
import interfaces.Observers.ObserverConstruction;
import interfaces.Observers.ObserverDomainReduction;
import main.Head;
import optimization.ObjectiveVariable;
import optimization.ObjectiveVariable.ObjVarGE;
import optimization.ObjectiveVariable.ObjVarLE;
import optimization.Optimizable;
import optimization.Optimizer;
import optimization.Optimizer.OptimizerDecreasing;
import optimization.Optimizer.OptimizerDichotomic;
import optimization.Optimizer.OptimizerIncreasing;
import propagation.Forward;
import solver.Solver;
import utility.Enums.EExportMode;
import utility.Kit;
import utility.Reflector;
import variables.Domain;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

public class Problem extends ProblemIMP implements ObserverConstruction {
	public static final Boolean DONT_KNOW = null;
	public static final Boolean STARRED = Boolean.TRUE;
	public static final Boolean UNSTARRED = Boolean.FALSE;

	public static final String AUXILIARY_VARIABLE_PREFIX = "aux_";

	private Variable[] prioritySumVars(Variable[] scp, int[] coeffs) {
		assert coeffs == null || IntStream.range(0, coeffs.length - 1).allMatch(i -> coeffs[i] <= coeffs[i + 1]);
		int LIM = 3; // HARD CODING
		Term[] terms = new Term[Math.min(scp.length, 2 * LIM)];
		if (terms.length == scp.length)
			for (int i = 0; i < terms.length; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * scp[i].dom.intervalValue(), scp[i]);
		else {
			for (int i = 0; i < LIM; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * scp[i].dom.intervalValue(), scp[i]);
			for (int i = 0; i < LIM; i++)
				terms[LIM + i] = new Term((coeffs == null ? 1 : coeffs[scp.length - 1 - i]) * scp[scp.length - 1 - i].dom.intervalValue(),
						scp[scp.length - 1 - i]);
		}
		terms = Stream.of(terms).filter(t -> t.coeff < -2 || t.coeff > 2).sorted().toArray(Term[]::new); // we discard terms of small coeffs
		if (terms.length > 0) {
			Variable[] t = Stream.of(terms).map(term -> term.var).toArray(Variable[]::new);

			if (t.length > LIM)
				t = Arrays.copyOfRange(t, t.length - LIM, t.length);
			Variable[] tt = new Variable[t.length];
			for (int i = 0; i < t.length; i++)
				tt[i] = t[t.length - 1 - i];
			return tt;
		}
		return null;
	}

	@Override
	public void afterProblemConstruction() {
		control(Variable.areNumsNormalized(variables) && Constraint.areNumsNormalized(constraints), "Non normalized nums in the problem");
		control(Stream.of(variables).map(x -> x.id()).distinct().count() == variables.length, "Two variables have the same id");
		control((settings.framework == COP) == (optimizer != null), "Not a COP " + settings.framework + " " + (optimizer == null));

		Stream.of(variables).peek(x -> control(Stream.of(x.ctrs).noneMatch(c -> c.num == -1))).forEach(x -> x.dom.finalizeConstruction(variables.length + 1));

		ConflictsStructure.buildFor(this);

		priorityVars = priorityVars.length == 0 && annotations.decision != null ? (Variable[]) annotations.decision : priorityVars;
		if (settings.framework == COP
				&& (optimizer.ctr instanceof ObjectiveVariable || optimizer.ctr instanceof MaximumCstLE || optimizer.ctr instanceof MinimumCstGE))
			head.control.restarts.restartAfterSolution = true;

		boolean strong = false;
		if (settings.framework == COP && head.control.valh.optValHeuristic) { // TODO experimental
			Constraint c = ((Constraint) optimizer.ctr);
			if (c instanceof ObjectiveVariable) {
				Variable x = c.scp[0];
				x.heuristic = optimizer.minimization ? new First(x, false) : new Last(x, false);
				this.priorityVars = new Variable[] { x };
			} else if (c instanceof ExtremumCst) {
				if (strong)
					for (Variable x : c.scp)
						x.heuristic = optimizer.minimization ? new First(x, false) : new Last(x, false); // the boolean is dummy
			} else if (c instanceof NValuesCst) {
				assert c instanceof NValuesCstLE;
				if (strong)
					for (Variable x : c.scp)
						x.heuristic = new Values(x, false, c.scp);
			} else if (c instanceof SumWeighted) { // || c instanceof SumSimple) {
				int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
				Variable[] vars = prioritySumVars(c.scp, coeffs);
				if (vars != null) {
					for (Variable x : vars) {
						int coeff = c instanceof SumSimple ? 1 : coeffs[c.positionOf(x)];
						boolean f = optimizer.minimization && coeff >= 0 || !optimizer.minimization && coeff < 0;
						System.out.println("before " + x + " " + x.heuristic);
						x.heuristic = f ? new First(x, false) : new Last(x, false); // the boolean is dummy
						System.out.println("after " + x.heuristic);
					}
					this.priorityVars = vars;
				}
			}
		}

		// Variable[] scp = c.scp;
		// if (c instanceof SumSimple || c instanceof ExtremumCst || c instanceof ObjVar) {
		// for (Variable x : scp)
		// x.heuristicVal = optimizationPilot.minimization ? new First(x, false) : new Last(x, false); // the boolean is dummy
		// } else if (c instanceof SumWeighted) {
		// int[] coeffs = ((SumWeighted) optimizationPilot.ctr).coeffs;
		// // for (int i = 0; i < scp.length; i++) {
		// // boolean f = optimizationPilot.minimization && coeffs[i] >= 0 || !optimizationPilot.minimization && coeffs[i] < 0;
		// // System.out.println("before " + scp[i].heuristicVal);
		// // scp[i].heuristicVal = f ? new First(scp[i], false) : new Last(scp[i], false); // the boolean is dummy
		// // System.out.println("after " + scp[i].heuristicVal);
		// // }
		// } else {
		// assert c instanceof NValuesLE;
		// for (Variable x : scp)
		// x.heuristicVal = new Values(x, false, scp);
		// }
		// if (c instanceof ObjVar)
		// this.priorityVars = new Variable[] { scp[0] };
		// else if (c instanceof SumWeighted) {
		// int[] coeffs = ((SumWeighted) c).coeffs;
		// assert IntStream.range(0, coeffs.length - 1).allMatch(i -> coeffs[i] <= coeffs[i + 1]);
		// int LIM = 3;
		// Term[] terms = new Term[Math.min(scp.length, 2 * LIM)];
		// if (terms.length == scp.length)
		// for (int i = 0; i < terms.length; i++)
		// terms[i] = new Term(coeffs[i] * scp[i].dom.highestValueDistance(), scp[i]);
		// else {
		// for (int i = 0; i < LIM; i++)
		// terms[i] = new Term(coeffs[i] * scp[i].dom.highestValueDistance(), scp[i]);
		// for (int i = 0; i < LIM; i++)
		// terms[LIM + i] = new Term(coeffs[scp.length - 1 - i] * scp[scp.length - 1 - i].dom.highestValueDistance(), scp[scp.length - 1 - i]);
		// }
		// terms = Stream.of(terms).filter(t -> t.coeff < -2 || t.coeff > 2).sorted().toArray(Term[]::new); // we discard terms of small coeffs
		// if (terms.length > 0) {
		// Variable[] t = Stream.of(terms).map(term -> term.var).toArray(Variable[]::new);
		//
		// if (t.length > LIM)
		// t = Arrays.copyOfRange(t, t.length - LIM, t.length);
		// Variable[] tt = new Variable[t.length];
		// for (int i = 0; i < t.length; i++)
		// tt[i] = t[t.length - 1 - i];
		// // for (int i = 0; i < tt.length; i++) {
		// // boolean f = optimizationPilot.minimization && coeffs[i] >= 0 || !optimizationPilot.minimization && coeffs[i] < 0;
		// // scp[i].heuristicVal = f ? new First(scp[i], false) : new Last(scp[i], false); // the boolean is dummy
		// // }
		// // this.priorityVars = tt;
		// }
		// }

	}

	@Override
	public void afterSolverConstruction() {
		Stream.of(variables).forEach(x -> x.dom.setPropagation(solver.propagation));
	}

	// ************************************************************************
	// ***** Class Symbolic
	// ************************************************************************

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

		// public String replaceSymbols(String s) {
		// for (Entry<String, Integer> entry : mapOfSymbols.entrySet())
		// s = s.replaceAll(entry.getKey(), entry.getValue() + "");
		// return s;
		// }
	}

	// ************************************************************************
	// ***** Fields
	// ************************************************************************

	public final Head head;

	/** The solver used to solve the problem. Alias for rs.solver. */
	public Solver solver;

	/**
	 * The set of variables of the problem, in the order they have been defined (posted).
	 */
	public Variable[] variables;

	/**
	 * The set of constraints of the problem, in the order they have been defined (posted).
	 */
	public Constraint[] constraints;

	/**
	 * The pilot for the objective of the problem. Maybe null.
	 */
	public Optimizer optimizer;

	/**
	 * The priority variables. For example, those that have to be assigned in priority by a backtrack search solver. There is 0 priority variable by default.
	 */
	public Variable[] priorityVars = new Variable[0];

	/**
	 * The priority variables put in the array above at indices ranging from 0 to this field value should be assigned strictly in that order.
	 */
	public int nStrictPriorityVars;

	/**
	 * An object used to record many data corresponding to metrics and various features of the problem.
	 */
	public Features features; // = new ProblemStuff(this);

	/**
	 * The object used to manage symbolic values. Basically, it transforms symbols into integers, but this is not visible for the user (modeler).
	 */
	public Symbolic symbolic = new Symbolic();

	public int nValuesRemoved; // sum over all variable domains

	/**
	 * The list of generators of an identified symmetry group of variables. Maybe, empty.
	 */
	public final List<List<int[]>> symmetryGroupGenerators = new ArrayList<>();

	/**
	 * The list of observers on domains. Whenever a domain is reduced, a callback function is called.
	 */
	public final Collection<ObserverDomainReduction> observersDomainReduction = new ArrayList<>();

	public final SettingGeneral settings;

	// ************************************************************************
	// ***** Parameters
	// ************************************************************************

	@Override
	public final String name() {
		String name = super.name();
		return name.matches("XCSP[23]-.*") ? name.substring(6) : name;
	}

	/**
	 * 
	 * /** Removes a constraint that has already been built. Should not be called when modeling. Advanced use.
	 */
	public void removeCtr(Constraint c) {
		// System.out.println("removed " + c + "size=" + stuff.collectedCtrsAtInit.size());
		control(constraints == null, "too late");
		features.collectedCtrsAtInit.remove(c);
		// maybe was not present
		Stream.of(c.scp).forEach(x -> x.collectedCtrs.remove(c));
		// TODO other things to do ??
		CtrAlone ca = ctrEntities.ctrToCtrAlone.get(c); // remove(c);
		ctrEntities.allEntities.remove(ca);
		ctrEntities.ctrToCtrAlone.remove(c);
	}

	/**
	 * Adds a constraint that has already been built. Should not be called when modeling. Advanced use.
	 */
	public final CtrAlone addCtr(Constraint c, TypeClass... classes) {
		// if (rs.cp.cpv.selectedVars != null) {
		// // boolean mustDiscard = false;
		// // if (resolution.cfg.extendSelectedVars) {
		// // if (resolution.cfg.selectedVars[0] instanceof Integer)
		// // mustDiscard = !Stream.of(ctr.scp).map(x -> x.id).anyMatch(id -> Arrays.binarySearch(resolution.cfg.selectedVars, id) >= 0);
		// // else mustDiscard = !Stream.of(ctr.scp).map(x -> x.getName()).anyMatch(name ->Arrays.binarySearch(resolution.cfg.selectedVars,
		// // name) >= 0);
		// // } else
		// boolean mustDiscard = c.scp.length == 0 || Stream.of(c.scp).anyMatch(x -> x.num == Variable.UNSET_NUM);
		// System.out.println(mustDiscard + " " + c);
		// if (mustDiscard) {
		// stuff.nDiscardedCtrs++;
		// return ctrEntities.new CtrAloneDummy("Discarded constraint due to the set of selected variables");
		// }
		// }

		c.num = features.addCollectedConstraint(c);
		return ctrEntities.new CtrAlone(c, classes);
	}

	public final Optimizable addOptimizable(Constraint c) {
		c.num = features.addCollectedConstraint(c);
		return (Optimizable) c;
	}

	public void annotateValh(Variable[] vars, Class<? extends HeuristicValues> clazz) {
		if (settings.enableAnnotations)
			for (Variable x : vars)
				x.heuristic = Reflector.buildObject(clazz.getSimpleName(), HeuristicValues.class, new Object[] { x, null });
	}

	/**
	 * Method that resets the problem instance. Each variable and each constraint is reset. The specified Boolean parameter indicates whether the weighted
	 * degrees values must not be reset or not.
	 */
	public void reset() { // currently, used by HeadExtraction
		Stream.of(variables).forEach(x -> x.reset());
		Stream.of(constraints).forEach(c -> c.reset());
		Stream.of(constraints).forEach(c -> c.ignored = false);
		// stuff = new ProblemStuff(this); // TODO reset or building a new object ?
		nValuesRemoved = 0;
		if (settings.verbose > 0)
			log.info("Reset of problem instance");
	}

	public void reduceTo(boolean[] presentVariables, boolean[] presentConstraints) { // currently, used by HeadExtraction
		control(symmetryGroupGenerators.size() == 0 && presentVariables.length == variables.length && presentConstraints.length == constraints.length);
		assert Variable.firstWipeoutVariableIn(variables) == null && Variable.areNumsNormalized(variables) && Constraint.areNumsNormalized(constraints);
		priorityVars = IntStream.range(0, variables.length).filter(i -> presentVariables[i]).mapToObj(i -> variables[i]).toArray(Variable[]::new);
		for (Variable x : priorityVars)
			x.reset();
		for (int i = 0; i < constraints.length; i++)
			if (!(constraints[i].ignored = !presentConstraints[i]))
				constraints[i].reset();
		// stuff = new ProblemStuff(this); // TODO reset or building a new object ?
		nValuesRemoved = 0;
		if (settings.verbose > 0)
			log.info("Reduction to (#V=" + priorityVars.length + ",#C=" + Kit.countIn(true, presentConstraints) + ")");
	}

	public final Constraint addUniversalConstraintDynamicallyBetween(Variable x, Variable y) {
		assert x.getClass() == y.getClass();
		assert !Stream.of(y.ctrs).anyMatch(c -> c.scp.length == 2 && c.involves(x));
		assert solver.propagation instanceof Forward;

		CtrAlone ca = extension(vars(x, y), new int[0][], false, DONT_KNOW);
		Constraint c = (Constraint) ca.ctr; // (Constraint) buildCtrTrue(x, y).ctr;
		c.cloneStructures(false);
		constraints = features.collectedCtrsAtInit.toArray(new Constraint[features.collectedCtrsAtInit.size()]); // storeConstraintsToArray();
		x.whenFinishedProblemConstruction();
		y.whenFinishedProblemConstruction();
		// constraint.buildBitRmResidues();
		if (x.assigned())
			c.doPastVariable(x);
		if (y.assigned())
			c.doPastVariable(y);
		return c;
	}

	private void inferAdditionalConstraints() {
		if (head.control.problem.isSymmetryBreaking()) {
			int nBefore = features.collectedCtrsAtInit.size();
			for (Constraint c : features.collectedCtrsAtInit)
				if (Constraint.getSymmetryMatching(c.key) == null)
					Constraint.putSymmetryMatching(c.key, c.defineSymmetryMatching());
			IdentificationAutomorphism automorphismIdentification = new IdentificationAutomorphism(this);
			for (Constraint c : automorphismIdentification.buildVariableSymmetriesFor(variables, features.collectedCtrsAtInit))
				addCtr(c);
			features.addToMapForAutomorphismIdentification(automorphismIdentification);
			symmetryGroupGenerators.addAll(automorphismIdentification.getGenerators());
			features.nAddedCtrs += features.collectedCtrsAtInit.size() - nBefore;
		}
		if (head.control.constraints.inferAllDifferentNb > 0)
			features.addToMapForAllDifferentIdentification(new IdentificationAllDifferent(this));
	}

	/**
	 * This method is called when the initialization is finished in order to, among other things, put constraints into an array.
	 */
	public final void storeConstraintsToArray() {
		inferAdditionalConstraints();
		constraints = features.collectedCtrsAtInit.toArray(new Constraint[0]);
		for (Variable x : variables) {
			x.whenFinishedProblemConstruction();
			features.varDegrees.add(x.deg());
		}
		assert Variable.areNumsNormalized(variables);// && Constraint.areIdsNormalized(constraints); TODO
		// head.clearMapsUsedByConstraints();
	}

	public Variable findVarWithNumOrId(Object o) {
		String msg = "Check your configuration parameters -ins -pr1 or -pr2";
		if (o instanceof Integer) {
			int num = (Integer) o;
			control(0 <= num && num < variables.length, num + " is not a valid variable num. " + msg);
			control(variables[num].num != Variable.UNSET_NUM, "You cannot use the discarded variable whose (initial) num is " + num + ". " + msg);
			return variables[num];
		} else {
			Variable x = mapForVars.get(o);
			control(x != null, "The variable " + o + " cannot be found. " + msg);
			control(x.num != Variable.UNSET_NUM, "You cannot use the discarded variable " + o + ". " + msg);
			return x;
		}
	}

	private final void addUnaryConstraintsOfUserInstantiation() {
		SettingVars settings = head.control.variables;
		control(settings.instantiatedVars.length == settings.instantiatedVals.length,
				"In the given instantiation, the number of variables (ids or names) is different from the number of values.");
		for (int i = 0; i < settings.instantiatedVars.length; i++) {
			Variable x = findVarWithNumOrId(settings.instantiatedVars[i]);
			int v = settings.instantiatedVals[i];
			control(x.dom.presentValue(v), "Value " + v + " not present in domain of " + x + ". Check  -ins.");
			x.dom.removeValuesAtConstructionTime(w -> w != v);
		}
	}

	private final void reduceDomainsOfIsolatedVariables() {
		// TODO other frameworks ?
		boolean reduceIsolatedVars = head.control.variables.reduceIsolatedVars && settings.nSearchedSolutions == 1 && !head.control.problem.isSymmetryBreaking()
				&& settings.framework == TypeFramework.CSP;
		List<Variable> isolatedVars = new ArrayList<>(), fixedVars = new ArrayList<>();
		int nRemovedValues = 0;
		for (Variable x : features.collectedVarsAtInit) {
			if (x.ctrs.length == 0) {
				isolatedVars.add(x);
				if (reduceIsolatedVars) {
					nRemovedValues += x.dom.size() - 1;
					x.dom.removeValuesAtConstructionTime(v -> v != x.dom.firstValue()); // we arbitrarily keep the first value
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

	public int[][] buildTable(Constraint... ctrs) {
		Variable[] scp = distinctSorted(vars(Stream.of(ctrs).map(c -> c.scp).toArray()));
		int[][] vaps = Stream.of(ctrs).map(c -> IntStream.range(0, c.scp.length).map(i -> Utilities.indexOf(c.scp[i], scp)).toArray()).toArray(int[][]::new);
		int[][] tmps = Stream.of(ctrs).map(c -> c.tupleManager.localTuple).toArray(int[][]::new);
		List<int[]> list = new ArrayList<>();
		EnumerationCartesian ec = new EnumerationCartesian(Variable.domSizeArrayOf(scp, true));
		while (ec.hasNext()) {
			int[] tuple = ec.next();
			boolean inconsistent = false;
			for (int i = 0; !inconsistent && i < ctrs.length; i++) {
				int[] vap = vaps[i];
				int[] t = tmps[i];
				IntStream.range(0, t.length).forEach(j -> t[j] = tuple[vap[j]]);
				if (!ctrs[i].checkIndexes(t))
					inconsistent = true;
			}
			if (!inconsistent)
				list.add(IntStream.range(0, scp.length).map(i -> scp[i].dom.toVal(tuple[i])).toArray());
		}
		return Kit.intArray2D(list);
	}

	public Problem(ProblemAPI api, String modelVariant, String data, String dataFormat, boolean dataSaving, String[] argsForPb, Head head) {
		super(api, modelVariant, argsForPb);
		this.head = head;
		head.problem = this; // required because it is needed during the initialization of some objects
		head.observersConstruction.add(0, this); // "Must be the first in the list when calling onConstructionSolverFinished
		this.settings = head.control.general;
		this.features = new Features(this);
		head.output.beforeData();
		loadData(data, dataFormat, dataSaving);
		head.output.afterData();
		api.model();

		this.variables = features.collectedVarsAtInit.toArray(new Variable[features.collectedVarsAtInit.size()]);
		addUnaryConstraintsOfUserInstantiation();
		storeConstraintsToArray();
		// currently, only mono-objective optimization supported
		// if (Solver.class.getSimpleName().equals(head.control.solving.clazz))
		// optimizer = new OptimizerBasic(this, "#violatedConstraints");

		reduceDomainsOfIsolatedVariables();
	}

	public final void display() {
		if (settings.verbose >= 2) {
			log.finer("\nProblem " + name());
			Stream.of(variables).forEach(x -> x.display(settings.verbose == 3));
			Stream.of(constraints).forEach(c -> c.display(settings.verbose == 3));
		}
	}

	public List<String> undisplay = new ArrayList<>();

	public void undisplay(String... names) {
		// Kit.control(Arrays.stream(names).allMatch(s -> varIds.contains(s)));
		undisplay = Arrays.asList(names);
	}

	// ************************************************************************
	// ***** Posting variables
	// ************************************************************************

	@Override
	public Class<VariableInteger> classVI() {
		return VariableInteger.class;
	}

	@Override
	public Class<VariableSymbolic> classVS() {
		return VariableSymbolic.class;
	}

	/** A map that gives access to each variable through its id. */
	public final Map<String, Variable> mapForVars = new HashMap<>();

	@Override
	public TypeFramework typeFramework() {
		return settings.framework;
	}

	/**
	 * Adds a variable that has already be built. Should not be called directly when modeling.
	 */
	public final Variable addVar(Variable x) {
		control(!mapForVars.containsKey(x.id()), x.id() + " duplicated");
		if (features.mustDiscard(x))
			return null;
		x.num = features.addCollectedVariable(x);
		mapForVars.put(x.id(), x);
		return x;
	}

	@Override
	public VariableInteger buildVarInteger(String id, Dom dom) {
		VariableInteger x = null;
		if (dom.values.length == 1 && dom.values[0] instanceof IntegerInterval)
			x = new VariableInteger(this, id, (IntegerInterval) dom.values[0]);
		else {
			// TODO use a cache here to avoid building the array of values several times?
			x = new VariableInteger(this, id, IntegerEntity.toIntArray((IntegerEntity[]) dom.values, Integer.MAX_VALUE)); // MAX_VALUE is a limit
		}
		return (VariableInteger) addVar(x);
	}

	@Override
	public VariableSymbolic buildVarSymbolic(String id, DomSymbolic dom) {
		return (VariableSymbolic) addVar(new VariableSymbolic(this, id, (String[]) dom.values));
	}

	/*********************************************************************************************/
	/**** Posting Constraints */
	/*********************************************************************************************/

	public boolean isBasicType(int type) {
		return type == 0;
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

	private Variable[][] translate2D(IVar[][] m) {
		return m instanceof Variable[][] ? (Variable[][]) m : Stream.of(m).map(t -> translate(t)).toArray(Variable[][]::new);
	}

	private Object unimplementedCase(Object... objects) {
		System.out.println("\n\n**********************");
		System.out.println("Missing Implementation");
		StackTraceElement[] t = Thread.currentThread().getStackTrace();
		System.out.println("  Method " + t[2].getMethodName());
		System.out.println("  Class " + t[2].getClassName());
		System.out.println("  Line " + t[2].getLineNumber());
		System.out.println("**********************");
		System.out.println(Stream.of(objects).filter(o -> o != null).map(o -> o.toString()).collect(Collectors.joining("\n")));
		// throw new RuntimeException();
		System.exit(1);
		return null;
	}

	private Range range(int length) {
		return new Range(length);
	}

	private String idAux() {
		return AUXILIARY_VARIABLE_PREFIX + varEntities.allEntities.size();
	}

	public Variable replaceByVariable(XNode<IVar> tree) {
		// int[] values = tree.getType().isPredicateOperator() ? new int[] { 0, 1 } : new
		// EvaluationManager(tree).generatePossibleValues(Variable.initDomainValues(vars(tree)));

		Object values = tree.possibleValues();
		Dom dom = values instanceof Range ? api.dom((Range) values) : api.dom((int[]) values);
		Var aux = api.var(idAux(), dom, "auxiliary variable");
		if (Constraint.howManyVarsWithin(vars(tree), head.control.propagation.spaceLimitation) == ALL) {
			int[][] tuples = new TreeEvaluator(tree).computeTuples(Variable.initDomainValues(vars(tree)));
			extension(vars(tree, aux), tuples, true); // extension(eq(aux, tree));
		} else
			equal(aux, tree);
		return (Variable) aux;
	}

	// ************************************************************************
	// ***** Constraint intension
	// ************************************************************************

	private XNode change(XNodeParent<IVar> tree) {
		System.out.println("change " + tree);
		for (int i = 0; i < tree.sons.length; i++) {
			if (tree.sons[i] instanceof XNodeParent)
				tree.sons[i] = change((XNodeParent) tree.sons[i]);
		}
		assert Stream.of(tree.sons).allMatch(son -> son instanceof XNodeLeaf);
		Variable aux = replaceByVariable(tree);
		return new XNodeLeaf<>(TypeExpr.VAR, aux);
	}

	// binary
	private Matcher x_relop_y = new Matcher(node(relop, var, var));
	private Matcher x_ariop_y__relop_k = new Matcher(node(relop, node(ariop, var, var), val));
	private Matcher k_relop__x_ariop_y = new Matcher(node(relop, val, node(ariop, var, var)));
	private Matcher x_relop__y_ariop_k = new Matcher(node(relop, var, node(ariop, var, val)));
	private Matcher y_ariop_k__relop_x = new Matcher(node(relop, node(ariop, var, val), var));
	private Matcher logic_y_relop_k__eq_x = new Matcher(node(TypeExpr.EQ, node(relop, var, val), var));
	private Matcher logic_k_relop_y__eq_x = new Matcher(node(TypeExpr.EQ, node(relop, val, var), var));
	private Matcher unalop_x__eq_y = new Matcher(node(TypeExpr.EQ, node(unalop, var), var));

	// ternary
	private Matcher x_ariop_y__relop_z = new Matcher(node(relop, node(ariop, var, var), var));
	private Matcher z_relop__x_ariop_y = new Matcher(node(relop, var, node(ariop, var, var)));
	private Matcher logic_y_relop_z__eq_x = new Matcher(node(TypeExpr.EQ, node(relop, var, var), var));

	// extremum
	private Matcher min_relop = new Matcher(node(relop, min_vars, varOrVal));
	private Matcher max_relop = new Matcher(node(relop, max_vars, varOrVal));

	private Matcher logic_X__eq_x = new Matcher(node(TypeExpr.EQ, logic_vars, var));

	// sum
	private Matcher add_vars__relop = new Matcher(node(relop, add_vars, varOrVal));
	private Matcher add_mul_vals__relop = new Matcher(node(relop, add_mul_vals, varOrVal));
	private Matcher add_mul_vars__relop = new Matcher(node(relop, add_mul_vars, varOrVal));

	private Condition basicCondition(XNodeParent<IVar> tree) {
		if (tree.type.isRelationalOperator() && tree.sons.length == 2 && tree.sons[1].type.oneOf(VAR, LONG))
			return tree.sons[1].type == VAR ? new ConditionVar(tree.relop(0), tree.sons[1].var(0)) : new ConditionVal(tree.relop(0), tree.sons[1].val(0));
		return null;
	}

	@Override
	public final CtrEntity intension(XNodeParent<IVar> tree) {
		tree = (XNodeParent<IVar>) tree.canonization(); // first, the tree is canonized
		Variable[] scp = (Variable[]) tree.vars();
		assert Variable.haveSameType(scp);
		int arity = scp.length;

		if (arity == 1) {
			if (head.mustPreserveUnaryConstraints()) {
				if (!head.control.constraints.intensionToExtensionUnaryCtrs)
					return addCtr(new Intension(this, scp, tree));
				TreeEvaluator evaluator = new TreeEvaluator(tree, symbolic.mapOfSymbols);
				int[] conflicts = scp[0].dom.valuesChecking(va -> evaluator.evaluate(va) != 1);
				if (conflicts.length < scp[0].dom.size() / 2)
					return addCtr(new Extension1(this, scp, conflicts, false));
				return addCtr(new Extension1(this, scp, scp[0].dom.valuesChecking(va -> evaluator.evaluate(va) == 1), true));
			}
			TreeEvaluator evaluator = new TreeEvaluator(tree, symbolic.mapOfSymbols);
			scp[0].dom.removeValuesAtConstructionTime(v -> evaluator.evaluate(v) != 1);
			features.nRemovedUnaryCtrs++;
			return ctrEntities.new CtrAloneDummy("Removed unary constraint by domain reduction");
		}

		long al = head.control.extension.arityLimitForIntensionToExtension, vl = head.control.extension.validLimitForIntensionToExtension;
		if (arity <= al && Domain.nValidTuplesBoundedAtMaxValueFor(scp) <= vl && Stream.of(scp).allMatch(x -> x instanceof Var)) {
			features.nConvertedConstraints++;
			return extension(tree);
		}

		// System.out.println("treeee " + tree + " " + vars.length + " " + head.control.xml.primitiveTernaryInSolver);
		SettingXml settings = head.control.xml;
		if (arity == 2 && settings.primitiveBinaryInSolver) {
			Constraint c = null;
			if (x_relop_y.matches(tree))
				c = PrimitiveBinarySub.buildFrom(this, scp[0], scp[1], tree.relop(0), 0);
			else if (x_ariop_y__relop_k.matches(tree))
				c = PrimitiveBinaryWithCst.buildFrom(this, scp[0], tree.ariop(0), scp[1], tree.relop(0), tree.val(0));
			else if (k_relop__x_ariop_y.matches(tree))
				c = PrimitiveBinaryWithCst.buildFrom(this, scp[0], tree.ariop(0), scp[1], tree.relop(0).arithmeticInversion(), tree.val(0));
			else if (x_relop__y_ariop_k.matches(tree))
				c = PrimitiveBinaryWithCst.buildFrom(this, scp[0], tree.relop(0), scp[1], tree.ariop(0), tree.val(0));
			else if (y_ariop_k__relop_x.matches(tree))
				c = PrimitiveBinaryWithCst.buildFrom(this, scp[1], tree.relop(0).arithmeticInversion(), scp[0], tree.ariop(0), tree.val(0));
			else if (logic_y_relop_k__eq_x.matches(tree))
				c = PrimitiveBinaryLog.buildFrom(this, scp[1], scp[0], tree.relop(1), tree.val(0));
			else if (logic_k_relop_y__eq_x.matches(tree))
				c = PrimitiveBinaryLog.buildFrom(this, scp[1], scp[0], tree.relop(1).arithmeticInversion(), tree.val(0));
			else if (unalop_x__eq_y.matches(tree))
				c = PrimitiveBinaryEQWithUnaryOperator.buildFrom(this, scp[1], tree.unalop(0), scp[0]);
			if (c != null)
				return addCtr(c);
		}
		if (arity == 3 && settings.primitiveTernaryInSolver) {
			Constraint c = null;
			if (x_ariop_y__relop_z.matches(tree))
				c = PrimitiveTernary.buildFrom(this, scp[0], tree.ariop(0), scp[1], tree.relop(0), scp[2]);
			else if (z_relop__x_ariop_y.matches(tree))
				c = PrimitiveTernary.buildFrom(this, scp[1], tree.ariop(0), scp[2], tree.relop(0).arithmeticInversion(), scp[0]);
			else if (logic_y_relop_z__eq_x.matches(tree))
				c = PrimitiveTernaryLog.buildFrom(this, scp[2], scp[0], tree.relop(1), scp[1]);
			if (c != null)
				return addCtr(c);
		}
		if (settings.recognizeLogicInSolver) {
			if (logic_X__eq_x.matches(tree)) {
				// System.out.println(" yep " + tree);
				Constraint c = PrimitiveLogicEq.buildFrom(this, scp[scp.length - 1], tree.logop(0),
						IntStream.range(0, scp.length - 1).mapToObj(i -> scp[i]).toArray(Variable[]::new));
				if (c != null)
					return addCtr(c);
			}
		}
		if (settings.recognizeExtremumInSolver) {
			if (min_relop.matches(tree)) {
				// System.exit(1);
				return minimum((Var[]) tree.sons[0].vars(), basicCondition(tree));
			}
			if (max_relop.matches(tree)) {
				// System.exit(1);
				return maximum((Var[]) tree.sons[0].vars(), basicCondition(tree));
			}
		}
		if (settings.recognizeSumInSolver) {
			// System.out.println("tree " + tree);
			if (add_vars__relop.matches(tree)) {
				Var[] list = (Var[]) tree.sons[0].arrayOfVars();
				return sum(list, Kit.repeat(1, list.length), basicCondition(tree)); // TODO direct call ? without coeffs set to 1
			}
			if (add_mul_vals__relop.matches(tree)) {
				Var[] list = (Var[]) tree.sons[0].arrayOfVars();
				int[] coeffs = Stream.of(tree.sons[0].sons).mapToInt(s -> s.type == VAR ? 1 : s.val(0)).toArray();
				return sum(list, coeffs, basicCondition(tree));
			}
			if (add_mul_vars__relop.matches(tree)) {
				Var[] list = Stream.of(tree.sons[0].sons).map(s -> s.var(0)).toArray(Var[]::new);
				Var[] coeffs = Stream.of(tree.sons[0].sons).map(s -> s.var(1)).toArray(Var[]::new);
				return sum(list, coeffs, basicCondition(tree));
			}
		}

		// boolean replace = true;
		// boolean b = tree2.type == TypeExpr.EQ && tree2.sons.length == 2 && tree2.sons[1].type == TypeExpr.VAR;
		// if (!b) {
		// for (int i = 0; i < tree2.sons.length; i++) {
		// if (tree2.sons[i] instanceof XNodeParent)
		// tree2.sons[i] = change((XNodeParent) tree2.sons[i]);
		// }
		// }
		// System.out.println("tree3 " + tree2);
		return addCtr(new Intension(this, scp, tree));
	}

	// ************************************************************************
	// ***** Converting intension to extension
	// ************************************************************************

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
			EExportMode exportMode = EExportMode.EXTENSION; // later, maybe a control parameter
			return new ModifiableBoolean(exportMode != EExportMode.EXTENSION_SUPPORTS && exportMode != EExportMode.EXTENSION_CONFLICTS ? null
					: exportMode == EExportMode.EXTENSION_SUPPORTS);
		}
	};

	@Override
	protected Converter getConverter() {
		return converter;
	}

	// ************************************************************************
	// ***** Constraint extension
	// ************************************************************************

	public final CtrAlone extension(IVar[] scp, Object[] tuples, boolean positive, Boolean starred) {
		if (tuples.length == 0)
			return addCtr(positive ? new CtrHardFalse(this, translate(scp), "Table constraint with 0 support") : new CtrHardTrue(this, translate(scp)));

		return addCtr(Extension.build(this, translate(scp), tuples, positive, starred));
	}

	@Override
	public final CtrAlone extension(Var[] scp, int[][] tuples, boolean positive) {
		return extension(scp, tuples, positive, DONT_KNOW);
	}

	@Override
	public final CtrAlone extension(VarSymbolic[] scp, String[][] tuples, boolean positive) {
		return extension(scp, tuples, positive, DONT_KNOW);
	}

	@Override
	public final CtrAlone extension(Var[] scp, AbstractTuple[] tuples, boolean positive) {
		return (CtrAlone) unimplementedCase();
	}

	// ************************************************************************
	// ***** Constraints regular and mdd
	// ************************************************************************

	@Override
	public final CtrAlone regular(Var[] list, Automaton automaton) {
		return addCtr(new ExtensionMDD(this, translate(list), automaton));
	}

	@Override
	public final CtrAlone mdd(Var[] list, Transition[] transitions) {
		return addCtr(new ExtensionMDD(this, translate(list), transitions));
	}

	public final CtrAlone mdd(Var[] list, int[][] tuples) {
		return addCtr(new ExtensionMDD(this, translate(list), tuples));
	}

	// public final CtrAlone mddOr(Var[] scp, MDDCD[] t) {
	// return addCtr(new CtrOrMDD(this, translate(scp), t));
	// }

	// ************************************************************************
	// ***** Constraint allDifferent
	// ************************************************************************

	private CtrEntity allDifferent(Variable[] scp) {
		if (scp.length <= 1)
			return ctrEntities.new CtrAloneDummy("Removed alldiff constraint with scope length = " + scp.length);
		if (isBasicType(head.control.global.typeAllDifferent))
			return addCtr(Variable.isPermutationElligible(scp) ? new AllDifferentPermutation(this, scp) : new AllDifferentComplete(this, scp));
		if (head.control.global.typeAllDifferent == 1)
			return forall(range(scp.length).range(scp.length), (i, j) -> {
				if (i < j)
					addCtr(new SubNE2(this, scp[i], scp[j], 0)); // different(scp[i], scp[j]);
			});
		if (head.control.global.typeAllDifferent == 2)
			return addCtr(new AllDifferentWeak(this, scp));
		if (head.control.global.typeAllDifferent == 3)
			return addCtr(new AllDifferentCounting(this, scp));
		if (head.control.global.typeAllDifferent == 4)
			return addCtr(new AllDifferentBound(this, scp));
		throw new UnsupportedOperationException();
	}

	@Override
	public final CtrEntity allDifferent(Var[] list) {
		return allDifferent(translate(list));
	}

	@Override
	public final CtrEntity allDifferent(VarSymbolic[] list) {
		return allDifferent(translate(list));
	}

	@Override
	public final CtrEntity allDifferent(Var[] scp, int[] exceptValues) {
		control(exceptValues.length >= 1);
		if (head.control.global.typeAllDifferent <= 1)
			return forall(range(scp.length).range(scp.length), (i, j) -> {
				if (i < j)
					intension(or(ne(scp[i], scp[j]), exceptValues.length == 1 ? eq(scp[i], exceptValues[0]) : in(scp[i], exceptValues)));
			});
		if (head.control.global.typeAllDifferent == 2)
			return addCtr(new AllDifferentExceptWeak(this, translate(scp), exceptValues));
		throw new UnsupportedOperationException();
	}

	private CtrAlone distinctVectors(Variable[] t1, Variable[] t2) {
		control(Variable.areAllDistinct(vars(t1, t2)), "For the moment not handled");
		if (isBasicType(head.control.global.typeDistinctVectors2))
			return addCtr(ExtensionSmart.buildDistinctVectors(this, t1, t2)); // return addCtr(new DistinctVectors2(this, t1, t2)); // BUG TO BE
																				// FIXED
		if (head.control.global.typeDistinctVectors2 == 1) {
			if (head.control.global.smartTable)
				return addCtr(ExtensionSmart.buildDistinctVectors(this, t1, t2));
			if (head.control.global.jokerTable)
				return extension(vars(t1, t2), Table.shortTuplesFordNotEqualVectors(t1, t2), true);
		}
		throw new UnsupportedOperationException();
	}

	/**
	 * Builds a DistinctVectors constraint. The tuple of values corresponding to the assignment of the variables in the array specified as first parameter must
	 * be different from the tuple of values corresponding to the assignment of the variables in the array specified as second parameter.
	 */
	private CtrEntity distinctVectors(Variable[][] lists) {
		if (head.control.global.typeDistinctVectorsK == 1)
			return forall(range(lists.length).range(lists.length), (i, j) -> {
				if (i < j) {
					if (head.control.global.smartTable)
						addCtr(ExtensionSmart.buildDistinctVectors(this, lists[i], lists[j]));
					else if (head.control.global.jokerTable)
						extension(vars(lists[i], lists[j]), Table.shortTuplesFordNotEqualVectors(lists[i], lists[j]), true);
					else
						// addCtr(new DistinctVectors(this, lists[i], lists[j]));
						addCtr(ExtensionSmart.buildDistinctVectors(this, lists[i], lists[j]));
					// TODO java ace seriesJanvier2018/Crossword/Crossword-m1-ogd-puzzle/Crossword-ogd-p02.xml.lzma -varh=WdegOnDom -positive=str2 -s=all
					// not the same number of solution with Smart and DistinctVectors
				}
			});
		throw new UnsupportedOperationException();
	}

	@Override
	public final CtrEntity allDifferentList(Var[]... lists) {
		control(lists.length >= 2);
		Variable[][] m = translate2D(lists);
		return lists.length == 2 ? distinctVectors(m[0], m[1]) : distinctVectors(m);
	}

	@Override
	public final CtrEntity allDifferentMatrix(Var[][] matrix) {
		CtrArray ctrSet1 = forall(range(matrix.length), i -> allDifferent(matrix[i]));
		CtrArray ctrSet2 = forall(range(matrix[0].length), i -> allDifferent(api.columnOf(matrix, i)));
		return ctrSet1.append(ctrSet2);
	}

	@Override
	public CtrEntity allDifferent(XNode<IVar>[] trees) {
		Var[] aux = replaceByVariables(trees);
		return allDifferent(aux);
	}

	// ************************************************************************
	// ***** Constraint allEqual
	// ************************************************************************

	@Override
	public final CtrEntity allEqual(Var... scp) {
		// using a table on large instances of Domino is very expensive; using a smart table is also very expensive
		// return addCtr(new AllEqual(this, translate(scp)));
		// return extension(scp, allEqualTable(translate(scp)), true, false);
		return addCtr(ExtensionSmart.buildAllEqual(this, translate(scp)));
	}

	@Override
	public final CtrEntity allEqual(VarSymbolic... scp) {
		throw new UnsupportedOperationException("Not implemented");
	}

	@Override
	public final CtrEntity allEqualList(Var[]... lists) {
		throw new UnsupportedOperationException("not implemnted");
	}

	// ************************************************************************
	// ***** Constraint ordered/lexicographic
	// ************************************************************************

	/**
	 * Ensures that the specified array of variables is ordered according to the specified operator, when considering the associated lengths. We must have
	 * x[i]+lengths[i] op x[i+1]. Can be decomposed into a sequence of binary constraints.
	 */
	@Override
	public final CtrEntity ordered(Var[] list, int[] lengths, TypeOperatorRel op) {
		control(list != null && lengths != null && list.length == lengths.length + 1 && op != null);
		return forall(range(list.length - 1),
				i -> addCtr(PrimitiveBinarySub.buildFrom(this, (Variable) list[i], (Variable) list[i + 1], op.toConditionOperator(), -lengths[i])));
	}

	/**
	 * Ensures that the specified array of variables is ordered according to the specified operator, when considering the associated lengths. We must have
	 * list[i]+lengths[i] op list[i+1]. Can be decomposed into a sequence of binary constraints.
	 */
	@Override
	public final CtrEntity ordered(Var[] list, Var[] lengths, TypeOperatorRel op) {
		control(list != null && lengths != null && list.length == lengths.length + 1 && op != null);
		return forall(range(list.length - 1),
				i -> addCtr(PrimitiveTernaryAdd.buildFrom(this, (Variable) list[i], (Variable) lengths[i], op.toConditionOperator(), (Variable) list[i + 1])));
		// intension(XNodeParent.build(op.toExpr(), add(list[i], lengths[i]), list[i + 1])));
	}

	/**
	 * Builds and returns a Lexicographic constraint. The tuple of values corresponding to the assignment of the variables in the array specified as first
	 * parameter must be before the tuple of values corresponding to the assignment of the variables in the array specified as second parameter. The meaning of
	 * the relation "before" is given by the value of the specified operator that must be one value among LT, LE, GT, and GE.
	 */
	private final CtrAlone lexSimple(Var[] t1, Var[] t2, TypeOperatorRel op) {
		return addCtr(Lexicographic.buildFrom(this, translate(t1), translate(t2), op));
	}

	@Override
	public final CtrEntity lex(Var[][] lists, TypeOperatorRel op) {
		control(op != null);
		return forall(range(lists.length - 1), i -> lexSimple(lists[i], lists[i + 1], op));
	}

	@Override
	public final CtrEntity lexMatrix(Var[][] matrix, TypeOperatorRel op) {
		control(op != null);
		forall(range(matrix.length - 1), i -> lexSimple(matrix[i], matrix[i + 1], op));
		return forall(range(matrix[0].length - 1), j -> lexSimple(api.columnOf(matrix, j), api.columnOf(matrix, j + 1), op));
	}

	// ************************************************************************
	// ***** Constraint sum
	// ************************************************************************

	private static class Term implements Comparable<Term> {
		long coeff;
		Variable var;

		private Term(long coeff, Variable var) {
			this.coeff = coeff;
			this.var = var;
		}

		@Override
		public int compareTo(Term term) {
			return Long.compare(coeff, term.coeff);
		}

		@Override
		public String toString() {
			return coeff + "*" + var;
		}
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

	private Var[] replaceByVariables(XNode<IVar>[] trees) {
		IntToDom doms = i -> {
			Object values = trees[i].possibleValues();
			return values instanceof Range ? api.dom((Range) values) : api.dom((int[]) values);
		};
		int aie = head.control.extension.arityLimitForIntensionToExtension, sl = head.control.propagation.spaceLimitation;
		if (trees.length > 1 && IntStream.range(1, trees.length).allMatch(i -> areSimilar(trees[0], trees[i]))) {
			Var[] aux = api.array(idAux(), api.size(trees.length), doms.apply(0), "auxiliary variables");
			int arity = trees[0].vars().length;
			int[][] tuples = arity <= aie && Constraint.howManyVarsWithin(vars(trees[0]), sl) == ALL
					? new TreeEvaluator(trees[0]).computeTuples(Variable.initDomainValues(vars(trees[0])))
					: null;
			for (int i = 0; i < trees.length; i++) {
				if (tuples != null) {
					extension(vars(trees[i], aux[i]), tuples, true); // extension(eq(aux[i], trees[i]));
					features.nConvertedConstraints++;
				} else
					equal(aux[i], trees[i]);
			}
			return aux;
		}

		Var[] aux = api.array(idAux(), api.size(trees.length), doms, "auxiliary variables");
		for (int i = 0; i < trees.length; i++) {
			int arity = trees[i].vars().length;
			if (arity <= aie && Constraint.howManyVarsWithin(vars(trees[i]), sl) == ALL) {
				int[][] tuples = new TreeEvaluator(trees[i]).computeTuples(Variable.currDomainValues(vars(trees[i])));
				extension(vars(trees[i], aux[i]), tuples, true); // extension(eq(aux[i], trees[i]));
				features.nConvertedConstraints++;
			} else
				equal(aux[i], trees[i]);
		}
		return aux;
	}

	private Var[] replaceByVariables(Stream<XNode<IVar>> trees) {
		return replaceByVariables(trees.toArray(XNode[]::new));
	}

	private CtrAlone sum(Variable[] list, int[] coeffs, TypeConditionOperatorRel op, long limit, boolean inversable) {
		// we canonize terms (group together several occurrences of the same variables and discard terms of coefficient 0)
		Term[] terms = new Term[list.length];
		for (int i = 0; i < terms.length; i++)
			terms[i] = new Term(coeffs == null ? 1 : coeffs[i], list[i]);
		if (!Variable.areAllDistinct(list)) {
			Set<Entry<Variable, Long>> entries = Stream.of(terms).collect(groupingBy(t -> t.var, summingLong((Term t) -> (int) t.coeff))).entrySet();
			terms = entries.stream().map(e -> new Term(e.getValue(), e.getKey())).toArray(Term[]::new);
			log.info("Sum constraint with several ocurrences of the same variable");
		}
		terms = Stream.of(terms).filter(t -> t.coeff != 0).sorted().toArray(Term[]::new); // we discard terms of coeff 0 and sort them
		list = Stream.of(terms).map(t -> t.var).toArray(Variable[]::new);
		control(Stream.of(terms).allMatch(t -> Utilities.isSafeInt(t.coeff)));
		coeffs = Stream.of(terms).mapToInt(t -> (int) t.coeff).toArray();

		// we reverse if possible (to have some opportunity to have only coeffs equal to 1)
		if (inversable && coeffs[0] == -1 && coeffs[coeffs.length - 1] == -1) { // if only -1 since sorted
			Arrays.fill(coeffs, 1);
			op = op.arithmeticInversion();
			limit = -limit;
		}
		boolean only1 = coeffs[0] == 1 && coeffs[coeffs.length - 1] == 1; // if only 1 since sorted
		if (op == EQ) {
			boolean deceq = false; // hard coding for the moment
			if (deceq) {
				if (only1) {
					addCtr(new SumSimpleLE(this, list, limit));
					addCtr(new SumSimpleGE(this, list, limit));
				} else {
					addCtr(new SumWeightedLE(this, list, coeffs, limit));
					addCtr(new SumWeightedGE(this, list, coeffs, limit));
				}
				return null; // null because several constraints // TODO returning a special value?
				// return addCtr(new CtrExtensionMDD(this, list, coeffs, new Range(limit, limit+1))));
			}
		}

		if (only1) {
			// if (rs.cp.hardCoding.convertBooleanSumAsCountingCtr && op != NE && Variable.areInitiallyBoolean(list)) {
			// Kit.control(0 <= limit && limit <= list.length);
			// int l = (int) limit;
			// return op == LT ? api.atMost(vs, 1, l - 1)
			// : op == LE ? api.atMost(vs, 1, l) : op == GE ? api.atLeast(vs, 1, l) : op == GT ? api.atLeast(vs, 1, l + 1) : api.exactly(vs, 1, l);
			// }

			return addCtr(SumSimple.buildFrom(this, list, op, limit));
		}
		return addCtr(SumWeighted.buildFrom(this, list, coeffs, op, limit));
	}

	private CtrEntity sum(IVar[] list, int[] coeffs, TypeConditionOperatorRel op, long limit) {
		return sum(translate(list), coeffs, op, limit, true);
	}

	@Override
	public final CtrEntity sum(Var[] list, int[] coeffs, Condition condition) {
		control(Stream.of(list).noneMatch(x -> x == null), "A variable is null");
		control(list.length == coeffs.length, "the number of variables is different from the number of coefficients");

		Object rightTerm = condition.rightTerm(); // a constant, a variable, a range or an int array according to the type of the condition

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
			XNodeParent<IVar> tree = XNodeParent.build(condition.operatorTypeExpr(), coeffs[0] == 1 ? list[0] : api.mul(list[0], coeffs[0]), rightTerm);
			return extension(tree); // we directly generate a table constraint because the arity is 1 or 2
		}

		// then, we handle the cases when the condition involves a set operator (IN or NOTIN)
		if (condition instanceof ConditionSet) {
			TypeConditionOperatorSet op = ((ConditionSet) condition).operator;
			int[] t = condition instanceof ConditionIntset ? (int[]) rightTerm : null;
			int min = condition instanceof ConditionIntvl ? ((Range) rightTerm).start : t[0];
			int max = condition instanceof ConditionIntvl ? ((Range) rightTerm).stop - 1 : t[t.length - 1];
			if (op == TypeConditionOperatorSet.IN) {
				boolean mdd = false; // hard coding for the moment
				if (mdd)
					return addCtr(new ExtensionMDD(this, translate(list), coeffs, rightTerm));
				sum(list, coeffs, GE, min);
				sum(list, coeffs, LE, max);
				if (condition instanceof ConditionIntset) {
					for (int v = t[0], index = 0; v < t[t.length - 1]; v++) {
						if (v < t[index])
							sum(list, coeffs, NE, v);
						else
							index++;
					}
				}
			} else { // NOTIN
				if (condition instanceof ConditionIntvl)
					for (int v = min; v <= max; v++)
						sum(list, coeffs, NE, v);
				else
					for (int v : t)
						sum(list, coeffs, NE, v);
			}
			return null; // null because several constraints // TODO returning a special value?
		}

		// finally, we handle the cases where the condition involves a relational operator
		TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
		if (condition instanceof ConditionVal)
			return sum(list, coeffs, op, (long) rightTerm);
		return sum(vars(list, (Variable) rightTerm), api.vals(coeffs, -1), op, 0);
	}

	@Override
	public final CtrEntity sum(Var[] list, Var[] coeffs, Condition condition) {
		control(Stream.concat(Stream.of(list), Stream.of(coeffs)).noneMatch(x -> x == null), "A variable is null in these arrays");
		control(list.length == coeffs.length, "The number of variables is different from the number of coefficients");

		// we check first if we can handle a Boolean scalar constraint
		if (condition instanceof ConditionRel) {
			if (Variable.areAllInitiallyBoolean(translate(list)) && Variable.areAllInitiallyBoolean(translate(coeffs))) {
				TypeConditionOperatorRel op = ((ConditionRel) condition).operator;
				Object rightTerm = condition.rightTerm();
				if (condition instanceof ConditionVal && op != NE)
					return addCtr(SumScalarBooleanCst.buildFrom(this, translate(list), translate(coeffs), op, safeInt((long) rightTerm)));
				if (condition instanceof ConditionVar && op != NE && op != EQ)
					return addCtr(SumScalarBooleanVar.buildFrom(this, translate(list), translate(coeffs), op, (Variable) rightTerm));
			}
		}

		Var[] aux = replaceByVariables(IntStream.range(0, list.length).mapToObj(i -> api.mul(list[i], coeffs[i])));
		return sum(aux, Kit.repeat(1, list.length), condition);
	}

	@Override
	public CtrEntity sum(XNode<IVar>[] trees, int[] coeffs, Condition condition) {
		Var[] aux = replaceByVariables(trees);
		return sum(aux, coeffs, condition);
	}

	// ************************************************************************
	// ***** Constraint count
	// ************************************************************************

	private CtrEntity atLeast(Var[] list, int value, int k) {
		control(list.length != 0 && k >= 0);
		Variable[] scp = Stream.of(list).filter(x -> ((VariableInteger) x).dom.presentValue(value) && ((VariableInteger) x).dom.size() > 1)
				.toArray(Variable[]::new);
		int newK = k - (int) Stream.of(list).filter(x -> ((VariableInteger) x).dom.onlyContainsValue(value)).count();
		if (newK <= 0)
			return ctrEntities.new CtrAloneDummy("Removed constraint due to newk < 0");
		if (newK == scp.length)
			return forall(range(scp.length), i -> equal(scp[i], value));
		if (newK > scp.length)
			return addCtr(new CtrHardFalse(this, translate(list), "Constraint atLeast intially unsatisfiable"));
		return newK == 1 ? addCtr(new AtLeast1(this, scp, value)) : addCtr(new AtLeastK(this, scp, value, newK));
	}

	private CtrEntity atMost(Var[] list, int value, int k) {
		if (list.length == 0)
			return ctrEntities.new CtrAloneDummy("atMost with empty set");
		control(k >= 0);
		Variable[] scp = Stream.of(list).filter(x -> ((VariableInteger) x).dom.presentValue(value) && ((VariableInteger) x).dom.size() > 1)
				.toArray(Variable[]::new);
		int newK = k - (int) Stream.of(list).filter(x -> ((VariableInteger) x).dom.onlyContainsValue(value)).count();
		if (newK < 0)
			return addCtr(new CtrHardFalse(this, translate(list), "Constraint atMost intially unsatisfiable"));
		if (newK == 0)
			return forall(range(scp.length), i -> different(scp[i], value));
		if (newK >= scp.length)
			return ctrEntities.new CtrAloneDummy("atMost with newK greater than scp.length");
		return newK == 1 ? addCtr(new AtMost1(this, scp, value)) : addCtr(new AtMostK(this, scp, value, newK));
	}

	private CtrEntity exactly(Var[] list, int value, int k) {
		control(list.length != 0 && k >= 0);
		Variable[] scp = Stream.of(list).filter(x -> ((VariableInteger) x).dom.presentValue(value) && ((VariableInteger) x).dom.size() > 1)
				.toArray(Variable[]::new);
		int newK = k - (int) Stream.of(list).filter(x -> ((VariableInteger) x).dom.onlyContainsValue(value)).count();
		control(newK >= 0, "UNSAT, constraint Exactly with scope " + Kit.join(list) + " has already more than " + k + " variables equal to " + value);
		if (newK == 0)
			return forall(range(scp.length), i -> different(scp[i], value));
		if (newK == scp.length)
			return forall(range(scp.length), i -> equal(scp[i], value));
		control(newK < scp.length, "Instance is UNSAT, constraint Exactly with scope " + Kit.join(list) + " cannot have " + k + " variables equal to " + value);
		return newK == 1 ? addCtr(new Exactly1(this, scp, value)) : addCtr(new ExactlyK(this, scp, value, newK));
	}

	private CtrEntity among(Var[] list, int[] values, int k) {
		control(list.length >= k);
		if (list.length == k) {
			for (Var x : list) {
				Domain dom = ((VariableInteger) x).dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int v = dom.toVal(a);
					if (!Kit.isPresent(v, values))
						different(x, v);
				}
			}
			// TODO HERE !!!!!!!!!!!!!!!!!! replace this above with a return forall
			return null; // to be changed !!!
		} else
			return addCtr(new Among(this, (VariableInteger[]) list, values, k));
	}

	private CtrEntity count1(VariableInteger[] list, int[] values, TypeConditionOperatorRel op, long limit) {
		int l = Utilities.safeInt(limit);
		if (values.length == 1) {
			if (op == GE)
				return atLeast(list, values[0], l);
			else if (op == GT)
				return atLeast(list, values[0], l + 1);
			else if (op == LT)
				return atMost(list, values[0], l - 1);
			else if (op == LE)
				return atMost(list, values[0], l);
			else if (op == EQ)
				return exactly(list, values[0], l);
			else
				return unimplemented("count");
		} else {
			if (op == EQ)
				return among(list, values, l);
			else
				return unimplemented("count");
		}
	}

	private CtrEntity count2(VariableInteger[] list, int[] values, TypeConditionOperatorRel op, VariableInteger limit) {
		if (values.length == 1) {
			if (op == EQ)
				return addCtr(new ExactlyVarK(this, list, values[0], limit));
			else
				return unimplemented("count");
		} else
			return unimplemented("count");
	}

	@Override
	public final CtrEntity count(Var[] list, int[] values, Condition condition) {
		list = clean(list);
		if (condition instanceof ConditionVal)
			return count1((VariableInteger[]) list, values, ((ConditionVal) condition).operator, ((ConditionVal) condition).k);
		if (condition instanceof ConditionVar)
			return count2((VariableInteger[]) list, values, ((ConditionVar) condition).operator, (VariableInteger) ((ConditionVar) condition).x);
		unimplementedIf(condition instanceof ConditionIntvl, "count");
		return unimplemented("count");
	}

	@Override
	public final CtrEntity count(Var[] list, Var[] values, Condition condition) {
		list = clean(list);
		values = clean(values);
		return unimplemented("count");
	}

	// ************************************************************************
	// ***** Constraint nValues
	// ************************************************************************

	@Override
	public CtrEntity nValues(Var[] list, Condition condition) {
		list = clean(list);
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			int k = Utilities.safeInt(((ConditionVal) condition).k);
			if (op == GT && k == 1 || op == GE && k == 2) {
				if (isBasicType(head.control.global.typeNotAllEqual))
					return addCtr(new NotAllEqual(this, (VariableInteger[]) list));
				if (head.control.global.typeNotAllEqual == 1) {
					VariableInteger[] clone = (VariableInteger[]) list.clone();
					return intension(or(IntStream.range(0, list.length - 1).mapToObj(i -> XNodeParent.ne(clone[i], clone[i + 1])).toArray(Object[]::new)));
				}
			}
			if (op == LE || op == LT)
				return addCtr(new NValuesCstLE(this, (VariableInteger[]) list, op == LE ? k : k - 1));
			if (op == GE || op == GT)
				return addCtr(new NValuesCstGE(this, (VariableInteger[]) list, op == GE ? k : k + 1));
		} else if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			if (op == EQ)
				return addCtr(new NValuesVarEQ(this, (VariableInteger[]) list, (VariableInteger) ((ConditionVar) condition).x));
		}
		return unimplemented("nValues");
	}

	@Override
	public CtrEntity nValues(Var[] list, Condition condition, int[] exceptValues) {
		list = clean(list);
		return unimplemented("nValues");
	}

	// ************************************************************************
	// ***** Constraint cardinality
	// ************************************************************************

	private CtrArray postClosed(VariableInteger[] list, int[] values) {
		control(Stream.of(list).anyMatch(x -> !x.dom.areInitValuesSubsetOf(values)));
		return forall(range(list.length), i -> {
			if (!list[i].dom.areInitValuesSubsetOf(values))
				api.extension(list[i], api.select(values, v -> list[i].dom.presentValue(v)));
		});
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, int[] occurs) {
		control(values.length == occurs.length);
		list = clean(list);
		if (mustBeClosed && Stream.of(list).anyMatch(x -> !((VariableInteger) x).dom.areInitValuesSubsetOf(values))) // 2nd part =
			// relevance of closed
			postClosed((VariableInteger[]) list, values);
		// should we return an object composed of the array above and the constraint below? Would it be useful ?
		return addCtr(new CardinalityConstant(this, (VariableInteger[]) list, values, occurs));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, Var[] occurs) {
		control(values.length == occurs.length && Stream.of(occurs).noneMatch(x -> x == null));
		list = clean(list);
		if (mustBeClosed && Stream.of(list).anyMatch(x -> !((VariableInteger) x).dom.areInitValuesSubsetOf(values)))
			// 2nd part = relevance of closed
			postClosed((VariableInteger[]) list, values);
		// should we return an object composed of the array above and the array below? Would it be useful ?
		VariableInteger[] clone = (VariableInteger[]) list.clone();
		return forall(range(values.length), i -> api.exactly(clone, values[i], occurs[i]));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, int[] occursMin, int[] occursMax) {
		control(values.length == occursMin.length && values.length == occursMax.length);
		list = clean(list);
		return addCtr(new CardinalityConstant(this, (VariableInteger[]) list, values, occursMin, occursMax));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, int[] occurs) {
		control(values.length == occurs.length && Stream.of(values).noneMatch(x -> x == null));
		list = clean(list);
		return unimplemented("cardinality");
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, Var[] occurs) {
		control(values.length == occurs.length && Stream.of(values).noneMatch(x -> x == null) && Stream.of(occurs).noneMatch(x -> x == null));
		list = clean(list);
		return unimplemented("cardinality");
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, int[] occursMin, int[] occursMax) {
		control(values.length == occursMin.length && values.length == occursMax.length && Stream.of(values).noneMatch(x -> x == null));
		list = clean(list);
		return unimplemented("cardinality");
	}

	// ************************************************************************
	// ***** Constraint minimum/ maximum
	// ************************************************************************

	private final CtrEntity extremum(final Var[] list, Condition condition, boolean minimum) {
		Variable[] vars = (Variable[]) clean(list);
		if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			if (op != EQ)
				return unimplemented(minimum ? "minimum" : "maximum");
			Variable y = (Variable) ((ConditionVar) condition).x;
			if (vars.length == 1)
				return equal(y, vars[0]);
			if (Stream.of(vars).anyMatch(x -> x == y))
				return forall(range(vars.length), i -> {
					if (y != vars[i])
						if (minimum)
							lessEqual(y, vars[i]);
						else
							greaterEqual(y, vars[i]);
				});
			if (head.control.global.smartTable)
				return addCtr(minimum ? ExtensionSmart.buildMinimum(this, vars, y) : ExtensionSmart.buildMaximum(this, vars, y));
			return addCtr(minimum ? new Minimum(this, vars, y) : new Maximum(this, vars, y));
		}
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op != EQ && op != NE);
			int k = Utilities.safeInt(((ConditionVal) condition).k);
			if (op == LT || op == LE) {
				k = op == LE ? k : k - 1;
				return addCtr(minimum ? new MinimumCstLE(this, vars, k) : new MaximumCstLE(this, vars, k));
			}
			if (op == GT || op == GE) {
				k = op == GE ? k : k + 1;
				return addCtr(minimum ? new MinimumCstGE(this, vars, k) : new MaximumCstGE(this, vars, k));
			}
		}
		return unimplemented(minimum ? "minimum" : "maximum");
	}

	private final CtrEntity extremum(Var[] list, int startIndex, Var index, TypeRank rank, Condition condition, boolean minimum) {
		control(Stream.of(list).noneMatch(x -> x == null));
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
	// ***** Constraint element
	// ************************************************************************

	@Override
	public final CtrAlone element(Var[] list, int value) {
		return (CtrAlone) atLeast(list, value, 1);
	}

	@Override
	public final CtrAlone element(Var[] list, Var value) {
		// TODO using sentinelVal1, sentinelVal2 (for two values in dom(value)), and sentinelVar1, sentinelVar2 for two variables in list
		return (CtrAlone) unimplemented("element");
	}

	@Override
	public final CtrAlone element(Var[] list, int startIndex, Var index, TypeRank rank, int value) {
		unimplementedIf(startIndex != 0 || (rank != null && rank != TypeRank.ANY), "element");
		if (head.control.global.jokerTable)
			return extension(vars(index, list), Table.shortTuplesForElement(translate(list), (Variable) index, value), true);
		return addCtr(new ElementConstant(this, translate(list), (Variable) index, value));
	}

	@Override
	public final CtrAlone element(Var[] list, int startIndex, Var index, TypeRank rank, Var value) {
		unimplementedIf(startIndex != 0 || (rank != null && rank != TypeRank.ANY), "element");
		if (head.control.global.smartTable)
			return addCtr(ExtensionSmart.buildElement(this, translate(list), (Variable) index, (Variable) value));
		if (head.control.global.jokerTable)
			return extension(Utilities.indexOf(value, list) == -1 ? vars(index, list, value) : vars(index, list),
					Table.shortTuplesForElement(translate(list), (Variable) index, (Variable) value), true);
		return addCtr(new ElementVariable(this, translate(list), (Variable) index, (Variable) value));
	}

	/**
	 * Builds a binary extension constraint because the vector is an array of integer values (and not variables).
	 */
	private final CtrEntity element(int[] list, int startIndex, Var index, Var value, int startValue) {
		List<int[]> l = new ArrayList<>();
		Domain dx = ((Variable) index).dom, dz = ((Variable) value).dom;
		for (int a = dx.first(); a != -1; a = dx.next(a)) {
			int va = dx.toVal(a) - startIndex;
			if (0 <= va && va < list.length && dz.presentValue(list[va] - startValue))
				l.add(new int[] { va + startIndex, list[va] - startValue });
		}
		return api.extension(vars(index, value), org.xcsp.common.structures.Table.clean(l));
	}

	/**
	 * Builds a binary extension constraint because the vector is an array of integer values (and not variables).
	 */
	@Override
	public final CtrEntity element(int[] list, int startIndex, Var index, TypeRank rank, Var value) {
		// if (rs.cp.export)
		// return addCtr(RawElement.buildFrom(this, scope(index, value), Utilities.join(list), startIndex, index, rank, value));
		unimplementedIf(rank != null && rank != TypeRank.ANY, "element");
		return element(list, startIndex, index, value, 0);
	}

	// /**
	// * Builds a binary extension constraint. Indeed, the vector is an array of
	// integer values (and not variables) and one index is an integer value too.
	// */
	// public final CtrAlone element(VarInteger index1, int index2, int[][]
	// vector, VarInteger result) {
	// List<int[]> list = new ArrayList<>();
	// for (int a = index1.dom.firstIdx(); a != -1; a = index1.dom.nextIdx(a)) {
	// int v = index1.dom.toVal(a);
	// XUtility.control(0 <= v && v < vector.length, "One value of the the
	// variable index1 does not correspond to an index of the vector");
	// int w = vector[v][index2];
	// XUtility.control(result.dom.isPresentVal(w), "One value of the the
	// variable result is missing");
	// list.add(tuple(v, w));
	// }
	// return extension(vars(index1, result), Kit.intArray2D(list));
	// }
	//
	// /**
	// * Builds a binary extension constraint. Indeed, the vector is an array of
	// integer values (and not variables) and one index is an integer value too.
	// */
	// public final CtrAlone element(int index1, VarInteger index2, int[][]
	// vector, VarInteger result) {
	// return element(index2, vector[index1], result);
	//
	// // List<int[]> list = new ArrayList<>();
	// // for (int a = index2.dom.firstIdx(); a != -1; a =
	// index2.dom.nextIdx(a)) {
	// // int v = index2.dom.toVal(a);
	// // XUtility.control(0 <= v && v < vector[0].length, "One value of the the
	// variable index1 does not correspond to an index of the vector");
	// // int w = vector[index1][v];
	// // XUtility.control(result.dom.isPresentVal(w), "One value of the the
	// variable result is missing");
	// // list.add(tuple(v, w));
	// // }
	// // return extension(vars(index2, result), Kit.intArray2D(list));
	// }

	// public final CtrAlone element(VarInteger index, Predicate<Integer> cond,
	// VarInteger[] vector, VarInteger result, int startResult) {
	// XUtility.control(Kit.indexOf(index, vector) == -1 && index != result,
	// "index cannot be in vector or be the same variable as result");
	// int pos = Kit.indexOf(result, vector);
	// if (pos != -1) {
	// int[] tuple = repeat(Table.STAR, 1 + vector.length);
	// List<int[]> tuples = new ArrayList<>();
	// for (int a = index.dom.firstIdx(); a != -1; a = index.dom.nextIdx(a)) {
	// int v = index.dom.toVal(a);
	// if (cond.test(v)) {
	// int[] t = tuple.clone();
	// t[0] = v;
	// tuples.add(t);
	// } else if (0 <= v && v < vector.length) {
	// if (vector[v] == result) {
	// if (startResult == 0) {
	// int[] t = tuple.clone();
	// t[0] = v;
	// tuples.add(t);
	// }
	// } else {
	// for (int b = vector[v].dom.firstIdx(); b != -1; b =
	// vector[v].dom.nextIdx(b)) {
	// int w = vector[v].dom.toVal(b);
	// if (result.dom.isPresentVal(w - startResult)) {
	// int[] t = tuple.clone();
	// t[0] = v;
	// t[1 + v] = w; // + offset;
	// t[1 + pos] = w - startResult;
	// tuples.add(t);
	// } } } } }
	// int[][] m = Kit.intArray2D(tuples);
	// System.out.println("\nM3=\n" + Kit.join(m) + "\n => " + m.length +
	// "tuples");
	// return extension(vars(index, vector), Kit.intArray2D(tuples),
	// Option.STAR);
	// } else
	// return (CtrAlone) Kit.exit("unimplemented case ");
	// }

	public int[][] jokerTableForElement(Var[] list, Var index, Var value, int startValue) {
		Kit.control(Utilities.indexOf(index, list) == -1 && index != value, "index cannot be in vector or be the same variable as result");
		int pos = Utilities.indexOf(value, list);
		if (pos != -1) {
			int[] tuple = api.repeat(Constants.STAR, 1 + list.length);
			List<int[]> tuples = new ArrayList<>();
			for (int a = ((Variable) index).dom.first(); a != -1; a = ((Variable) index).dom.next(a)) {
				int v = ((Variable) index).dom.toVal(a);
				if (0 <= v && v < list.length) {
					if (list[v] == value) {
						if (startValue == 0) {
							int[] t = tuple.clone();
							t[0] = v;
							tuples.add(t);
						}
					} else {
						for (int b = ((Variable) list[v]).dom.first(); b != -1; b = ((Variable) list[v]).dom.next(b)) {
							int w = ((Variable) list[v]).dom.toVal(b);
							if (((Variable) value).dom.presentValue(w - startValue)) {
								int[] t = tuple.clone();
								t[0] = v;
								t[1 + v] = w; // + offset;
								t[1 + pos] = w - startValue;
								tuples.add(t);
							}
						}
					}
				}
			}
			// System.out.println(Kit.join(Kit.intArray2D(tuples)));
			return Kit.intArray2D(tuples);
		} else
			return (int[][]) Kit.exit("unimplemented case ");
	}

	@Override
	public CtrEntity element(int[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, Var value) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		List<int[]> l = new ArrayList<>();
		Domain dx = ((Variable) rowIndex).dom, dy = ((Variable) colIndex).dom, dz = ((Variable) value).dom;
		for (int a = dx.first(); a != -1; a = dx.next(a))
			for (int b = dy.first(); b != -1; b = dy.next(b)) {
				int i = dx.toVal(a), j = dy.toVal(b);
				if (0 <= i && i < matrix.length && 0 <= j && j < matrix[i].length && dz.presentValue(matrix[i][j]))
					l.add(new int[] { i, j, matrix[i][j] });
			}
		return api.extension(vars(rowIndex, colIndex, value), org.xcsp.common.structures.Table.clean(l));
	}

	@Override
	public CtrEntity element(Var[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, int value) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		if (rowIndex == colIndex) {
			control(matrix.length == matrix[0].length);
			Var[] t = IntStream.range(0, matrix.length).mapToObj(i -> matrix[i][i]).toArray(Var[]::new);
			return element(t, startRowIndex, rowIndex, null, value);
		}
		return addCtr(new ElementMatrix(this, (Variable[][]) matrix, (Variable) rowIndex, (Variable) colIndex, value));
	}

	// ************************************************************************
	// ***** Constraint channel
	// ************************************************************************

	@Override
	public CtrEntity channel(Var[] list, int startIndex) {
		control(Stream.of(list).noneMatch(x -> x == null));
		return unimplemented("channel");
	}

	@Override
	public CtrEntity channel(Var[] list1, int startIndex1, Var[] list2, int startIndex2) {
		control(Stream.of(list1).noneMatch(x -> x == null) && Stream.of(list2).noneMatch(x -> x == null));
		control(startIndex1 == 0 && startIndex2 == 0, "unimplemented case for channel");
		// TODO : the two constraints above are not included in the object that is returned. Is that a problem?
		if (list1.length == list2.length) {
			allDifferent(list1);
			allDifferent(list2);
		}
		return forall(range(list1.length), i -> api.element(list2, list1[i], i));
	}

	@Override
	public final CtrEntity channel(Var[] list, int startIndex, Var value) {
		control(Stream.of(list).noneMatch(x -> x == null));
		control(startIndex == 0);
		control(Variable.areAllInitiallyBoolean((VariableInteger[]) list) && ((VariableInteger) value).dom.areInitValuesExactly(range(list.length)));
		return forall(range(list.length), i -> intension(iff(list[i], eq(value, i))));
	}

	// ************************************************************************
	// ***** Constraint stretch
	// ************************************************************************

	@Override
	public CtrEntity stretch(Var[] list, int[] values, int[] widthsMin, int[] widthsMax, int[][] patterns) {
		control(values.length == widthsMin.length && values.length == widthsMax.length);
		control(IntStream.range(0, values.length).allMatch(i -> widthsMin[i] <= widthsMax[i]));
		control(patterns == null || Stream.of(patterns).allMatch(t -> t.length == 2));
		return unimplemented("strtech");
	}

	// ************************************************************************
	// ***** Constraint noOverlap
	// ************************************************************************

	private CtrAlone noOverlap(Var x1, Var x2, int w1, int w2) {
		if (isBasicType(head.control.global.typeNoOverlap))
			return addCtr(new Disjonctive(this, (Variable) x1, w1, (Variable) x2, w2));
		if (head.control.global.typeNoOverlap == 2)
			return (CtrAlone) intension(or(le(add(x1, w1), x2), le(add(x2, w2), x1)));
		if (head.control.global.typeNoOverlap == 10) // rs.cp.global.smartTable)
			return addCtr(ExtensionSmart.buildNoOverlap(this, (Variable) x1, (Variable) x2, w1, w2));
		// if (rs.cp.constraints.useGlobalCtrs)
		// return addCtr(new Disjonctive(this, (Variable) x1, w1, (Variable) x2, w2));
		return (CtrAlone) Kit.exit("Bad value for the choice of the propagator");
	}

	@Override
	public final CtrEntity noOverlap(Var[] origins, int[] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		return forall(range(origins.length).range(origins.length), (i, j) -> {
			if (i < j)
				noOverlap(origins[i], origins[j], lengths[i], lengths[j]);
		});
	}

	@Override
	public final CtrEntity noOverlap(Var[] origins, Var[] lengths, boolean zeroIgnored) {
		return unimplemented("noOverlap");
	}

	private void addNonOverlapTuplesFor(List<int[]> list, Domain dom1, Domain dom2, int offset, boolean first, boolean xAxis) {
		for (int a = dom1.first(); a != -1; a = dom1.next(a)) {
			int va = dom1.toVal(a);
			for (int b = dom2.last(); b != -1; b = dom2.prev(b)) {
				int vb = dom2.toVal(b);
				if (va + offset > vb)
					break;
				list.add(xAxis ? api.tuple(first ? va : vb, first ? vb : va, STAR, STAR) : api.tuple(STAR, STAR, first ? va : vb, first ? vb : va));
			}
		}
	}

	private int[][] computeTable(Variable x1, Variable x2, Variable y1, Variable y2, int w1, int w2, int h1, int h2) {
		List<int[]> list = new ArrayList<int[]>();
		addNonOverlapTuplesFor(list, x1.dom, x2.dom, w1, true, true);
		addNonOverlapTuplesFor(list, x2.dom, x1.dom, w2, false, true);
		addNonOverlapTuplesFor(list, y1.dom, y2.dom, h1, true, false);
		addNonOverlapTuplesFor(list, y2.dom, y1.dom, h2, false, false);
		return Kit.intArray2D(list);
	}

	private CtrAlone noOverlap(Variable x1, Variable x2, Variable y1, Variable y2, int w1, int w2, int h1, int h2) {
		if (head.control.global.smartTable)
			return addCtr(ExtensionSmart.buildNoOverlap(this, x1, y1, x2, y2, w1, h1, w2, h2));
		if (head.control.global.jokerTable)
			return extension(vars(x1, x2, y1, y2), computeTable(x1, x2, y1, y2, w1, w2, h1, h2), true, true);
		return (CtrAlone) intension(or(le(add(x1, w1), x2), le(add(x2, w2), x1), le(add(y1, h1), y2), le(add(y2, h2), y1)));
	}

	@Override
	public final CtrEntity noOverlap(Var[][] origins, int[][] lengths, boolean zeroIgnored) {
		// Kit.control(Kit.isRectangular(origins) && Kit.isRectangular(lengths) )
		unimplementedIf(!zeroIgnored, "noOverlap");
		return forall(range(origins.length).range(origins.length), (i, j) -> {
			if (i < j)
				noOverlap((Variable) origins[i][0], (Variable) origins[j][0], (Variable) origins[i][1], (Variable) origins[j][1], lengths[i][0], lengths[j][0],
						lengths[i][1], lengths[j][1]);
		});
	}

	private CtrAlone noOverlap(Variable x1, Variable x2, Variable y1, Variable y2, Variable w1, Variable w2, Variable h1, Variable h2) {
		if (head.control.global.smartTable && Stream.of(w1, w2, h1, h2).allMatch(x -> x.dom.initSize() == 2))
			return addCtr(ExtensionSmart.buildNoOverlap(this, x1, y1, x2, y2, w1, h1, w2, h2));
		return (CtrAlone) intension(or(le(add(x1, w1), x2), le(add(x2, w2), x1), le(add(y1, h1), y2), le(add(y2, h2), y1)));
	}

	@Override
	public final CtrEntity noOverlap(Var[][] origins, Var[][] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		return forall(range(origins.length).range(origins.length), (i, j) -> {
			if (i < j)
				noOverlap((Variable) origins[i][0], (Variable) origins[j][0], (Variable) origins[i][1], (Variable) origins[j][1], (Variable) lengths[i][0],
						(Variable) lengths[j][0], (Variable) lengths[i][1], (Variable) lengths[j][1]);
		});
	}

	// ************************************************************************
	// ***** Constraint cumulative
	// ************************************************************************

	@Override
	public final CtrEntity cumulative(Var[] origins, int[] lengths, Var[] ends, int[] heights, Condition condition) {
		if (ends == null && condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			control(op == LT || op == LE);
			int limit = Utilities.safeInt(((ConditionVal) condition).k);
			return addCtr(new Cumulative(this, (Variable[]) origins, lengths, heights, op == LT ? limit + 1 : limit));
		}
		return unimplemented("cumulative");
	}

	@Override
	public final CtrEntity cumulative(Var[] origins, Var[] lengths, Var[] ends, int[] heights, Condition condition) {
		return unimplemented("cumulative");
	}

	@Override
	public final CtrEntity cumulative(Var[] origins, int[] lengths, Var[] ends, Var[] heights, Condition condition) {
		return unimplemented("cumulative");
	}

	@Override
	public final CtrEntity cumulative(Var[] origins, Var[] lengths, Var[] ends, Var[] heights, Condition condition) {
		return unimplemented("cumulative");
	}

	// ************************************************************************
	// ***** Constraint circuit
	// ************************************************************************

	@Override
	public CtrEntity circuit(Var[] list, int startIndex) {
		unimplementedIf(startIndex != 0, "circuit");
		return addCtr(new Circuit(this, translate(list)));
	}

	@Override
	public CtrEntity circuit(Var[] list, int startIndex, int size) {
		return unimplemented("circuit");
	}

	@Override
	public CtrEntity circuit(Var[] list, int startIndex, Var size) {
		return unimplemented("circuit");
	}

	// ************************************************************************
	// ***** Constraint clause
	// ************************************************************************

	@Override
	public final CtrEntity clause(Var[] list, Boolean[] phases) {
		Kit.control(Stream.of(list).noneMatch(x -> x == null), "A variable in array list is null");
		Kit.control(list.length == phases.length, "Bad form of clause");
		Kit.control(Variable.areAllInitiallyBoolean((VariableInteger[]) list), "A variable is not Boolean in the array list.");
		if (head.control.global.typeClause == 1)
			return api.sum(list, Stream.of(phases).mapToInt(p -> p ? 1 : -1).toArray(), NE, -Stream.of(phases).filter(p -> !p).count());
		return unimplemented("clause");
	}

	public final CtrEntity clause(Var[] pos, Var[] neg) {
		control(Stream.of(pos).noneMatch(x -> x == null) && Stream.of(neg).noneMatch(x -> x == null), "No null values is allowed in the specified arrays.");
		Boolean[] phases = IntStream.range(0, pos.length + neg.length).mapToObj(i -> (Boolean) (i < pos.length)).toArray(Boolean[]::new);
		return clause(vars(pos, (Object) neg), phases);
	}

	// ************************************************************************
	// ***** Constraint instantiation
	// ************************************************************************

	@Override
	public final CtrEntity instantiation(Var[] list, int[] values) {
		control(list.length == values.length && list.length > 0);
		control(IntStream.range(0, list.length).noneMatch(i -> !((Variable) list[i]).dom.presentValue(values[i])), "Pb");
		if (head.control.global.typeInstantiation == 1)
			return forall(range(list.length), i -> equal(list[i], values[i]));
		return unimplemented("instantiation");
	}

	// ************************************************************************
	// ***** Meta-Constraint slide
	// ************************************************************************

	@Override
	public final CtrEntity slide(IVar[] list, Range range, IntFunction<CtrEntity> template) {
		control(range.start == 0 && range.length() > 0);
		if (range.length() == 1)
			return template.apply(0);
		return manageLoop(() -> IntStream.range(0, range.stop).filter(i -> i % range.step == 0).mapToObj(i -> (Constraint) ((CtrAlone) template.apply(i)).ctr)
				.toArray(Constraint[]::new));
	}

	// ************************************************************************
	// ***** Meta-Constraints ifThen and ifThenElse
	// ************************************************************************

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
	public final CtrAlone smart(IVar[] scp, SmartTuple... smartTuples) {
		return addCtr(new ExtensionSmart(this, translate(scp), smartTuples));
	}

	// /**
	// * Builds a constraint that holds when at least k variables of the scope take the corresponding value in the specified tuple.
	// */
	// public CtrEntity tupleProximityGE(IVar[] scope, int[] tuple, int k) {
	// control(scope.length != 0);
	// // if (noModidictaion)
	// return addCtr(new HammingProximityConstantGE(this, translate(scope), tuple, k));
	// // List<IVar> newScope = new ArrayList<>();
	// // List<Integer> newTuple = new ArrayList<>();
	// // int newK = k;
	// // for (int i = 0; i < scope.length; i++)
	// // if (((Variable) scope[i]).dom.isPresentValue(tuple[i]))
	// // if (((Variable) scope[i]).dom.size() > 1) {
	// // newScope.add(scope[i]);
	// // newTuple.add(tuple[i]);
	// // } else
	// // newK--;
	// // if (newK <= 0)
	// // return ctrEntities.new CtrAloneDummy("Removed constraint due to newk <= 0");
	// // if (newK == newScope.size())
	// // return forall(range(scope.length), i -> equal(scope[i], tuple[i]));
	// // control(newK < newScope.size(), "Instance is UNSAT, constraint with scope " + Kit.join(scope) + " cannot have more than " + k
	// // + " variables equal to their corresponding value in " + Kit.join(tuple));
	// // return addCtr(new HammingProximityConstantGE(this, newScope.toArray(new Variable[newScope.size()]), Kit.intArray(newTuple), newK));
	// }
	//
	// public CtrEntity tupleProximityDistanceSum(IVar[] scope, int[] tuple, int k) {
	// return addCtr(new HammingProximityConstantSumLE(this, translate(scope), tuple, k));
	// }

	// ************************************************************************
	// ***** Managing objectives
	// ************************************************************************

	public final static String vfsComment = "Either you set -f=cop or you set -f=csp together with -vfs=v where v is an integer value forcing the value of the objective.";

	private Optimizer buildOptimizer(TypeOptimization opt, Optimizable clb, Optimizable cub) {
		control(optimizer == null, "Only mono-objective currently supported");
		head.control.toCOP();
		String suffix = Kit.camelCaseOf(head.control.optimization.strategy.name());
		if (suffix.equals("Decreasing"))
			return new OptimizerDecreasing(this, opt, clb, cub);
		if (suffix.equals("Increasing"))
			return new OptimizerIncreasing(this, opt, clb, cub);
		control(suffix.equals("Dichotomic"));
		return new OptimizerDichotomic(this, opt, clb, cub);

		// the code below must be changed, as for heuristics, if we want to use it, see in Head, HandlerClasses
		// return Reflector.buildObject(suffix, OptimizationPilot.class, this, opt, c);
	}

	private boolean switchToSatisfaction(TypeOptimization opt, TypeObjective obj, int[] coeffs, Variable... list) {
		int limit = settings.limitForSatisfaction;
		if (limit == PLUS_INFINITY_INT)
			return false;
		head.control.toCSP();
		if (obj == EXPRESSION) {
			control(list.length == 1 && coeffs == null);
			intension(opt == MINIMIZE ? XNodeParent.le(list[0], limit) : XNodeParent.ge(list[0], limit));
		} else if (coeffs != null) {
			control(obj == SUM);
			sum(list, coeffs, opt == MINIMIZE ? LE : GE, limit);
		} else {
			control(obj.generalizable());
			if (opt == MINIMIZE) {
				if (obj == SUM)
					addCtr(new SumSimpleLE(this, list, limit));
				else if (obj == MINIMUM)
					addCtr(new MinimumCstLE(this, list, limit));
				else if (obj == MAXIMUM)
					forall(range(list.length), i -> lessEqual(list[i], limit));
				else
					addCtr(new NValuesCstLE(this, list, limit));
			} else {
				if (obj == SUM)
					addCtr(new SumSimpleGE(this, list, limit));
				else if (obj == MINIMUM)
					forall(range(list.length), i -> greaterEqual(list[i], limit));
				else if (obj == MAXIMUM)
					addCtr(new MaximumCstGE(this, list, limit));
				else
					addCtr(new NValuesCstGE(this, list, limit));
			}
		}
		return true;
	}

	private ObjEntity optimize(TypeOptimization opt, IVar x) {
		if (!switchToSatisfaction(opt, EXPRESSION, null, (Variable) x)) {
			long lb = head.control.optimization.lb, ub = head.control.optimization.ub;
			optimizer = buildOptimizer(opt, addOptimizable(new ObjVarGE(this, (Variable) x, lb)), addOptimizable(new ObjVarLE(this, (Variable) x, ub)));
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

	@Override
	public final ObjEntity minimize(XNode<IVar> tree) {
		return minimize(replaceByVariable(tree));
	}

	@Override
	public final ObjEntity maximize(XNode<IVar> tree) {
		return maximize(replaceByVariable(tree));
	}

	private ObjEntity optimize(TypeOptimization opt, TypeObjective type, Variable[] list) {
		control(type.generalizable());
		if (!switchToSatisfaction(opt, type, null, list)) {
			long lb = head.control.optimization.lb, ub = head.control.optimization.ub;
			Constraint clb = type == SUM ? new SumSimpleGE(this, list, lb)
					: type == MINIMUM ? new MinimumCstGE(this, list, lb)
							: type == MAXIMUM ? new MaximumCstGE(this, list, lb) : new NValuesCstGE(this, list, lb);
			Constraint cub = type == SUM ? new SumSimpleLE(this, list, ub)
					: type == MINIMUM ? new MinimumCstLE(this, list, ub)
							: type == MAXIMUM ? new MaximumCstLE(this, list, ub) : new NValuesCstLE(this, list, ub);
			optimizer = buildOptimizer(opt, addOptimizable(clb), addOptimizable(cub));
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
		control(type == SUM && coeffs != null);
		if (!switchToSatisfaction(opt, type, coeffs, list)) {
			long lb = head.control.optimization.lb, ub = head.control.optimization.ub;
			optimizer = buildOptimizer(opt, (Optimizable) sum(list, coeffs, GE, lb, false).ctr, (Optimizable) sum(list, coeffs, LE, ub, false).ctr);
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

	@Override
	public ObjEntity minimize(TypeObjective type, XNode<IVar>[] trees) {
		return minimize(type, replaceByVariables(trees));
	}

	@Override
	public ObjEntity minimize(TypeObjective type, XNode<IVar>[] trees, int[] coeffs) {
		return minimize(type, replaceByVariables(trees), coeffs);
	}

	@Override
	public ObjEntity maximize(TypeObjective type, XNode<IVar>[] trees) {
		return maximize(type, replaceByVariables(trees));
	}

	@Override
	public ObjEntity maximize(TypeObjective type, XNode<IVar>[] trees, int[] coeffs) {
		return maximize(type, replaceByVariables(trees), coeffs);
	}

	/**********************************************************************************************
	 * Managing Annotations
	 *********************************************************************************************/

	@Override
	public void decisionVariables(IVar[] list) {
		if (settings.enableAnnotations)
			super.decisionVariables(list);
	}

}
