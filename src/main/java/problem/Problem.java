package problem;

import static java.util.stream.Collectors.groupingBy;
import static java.util.stream.Collectors.summingLong;
import static org.xcsp.common.Constants.ALL;
import static org.xcsp.common.Constants.PLUS_INFINITY;
import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.NE;
import static org.xcsp.common.Types.TypeObjective.EXPRESSION;
import static org.xcsp.common.Types.TypeObjective.MAXIMUM;
import static org.xcsp.common.Types.TypeObjective.MINIMUM;
import static org.xcsp.common.Types.TypeObjective.NVALUES;
import static org.xcsp.common.Types.TypeObjective.SUM;
import static org.xcsp.common.Types.TypeOptimization.MAXIMIZE;
import static org.xcsp.common.Types.TypeOptimization.MINIMIZE;
import static org.xcsp.common.Utilities.safeInt;
import static org.xcsp.common.predicates.XNodeParent.add;
import static org.xcsp.common.predicates.XNodeParent.eq;
import static org.xcsp.common.predicates.XNodeParent.iff;
import static org.xcsp.common.predicates.XNodeParent.in;
import static org.xcsp.common.predicates.XNodeParent.le;
import static org.xcsp.common.predicates.XNodeParent.ne;
import static org.xcsp.common.predicates.XNodeParent.or;
import static org.xcsp.modeler.definitions.ICtr.MATRIX;
import static utility.Kit.log;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.IntFunction;
import java.util.function.Predicate;
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
import org.xcsp.common.domains.Values.IntegerValue;
import org.xcsp.common.enumerations.EnumerationCartesian;
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

import constraints.Constraint;
import constraints.CtrHard;
import constraints.CtrRaw.RawAllDifferent;
import constraints.hard.CtrExtension;
import constraints.hard.CtrHardFalse;
import constraints.hard.CtrHardTrue;
import constraints.hard.CtrIntension;
import constraints.hard.extension.CtrExtensionMDD;
import constraints.hard.extension.CtrExtensionOrMDD;
import constraints.hard.extension.CtrExtensionSmart;
import constraints.hard.extension.structures.MDDCD;
import constraints.hard.extension.structures.SmartTuple;
import constraints.hard.extension.structures.Table;
import constraints.hard.global.AllDifferent;
import constraints.hard.global.AllDifferentBound;
import constraints.hard.global.AllDifferentCounting;
import constraints.hard.global.AllDifferentExceptWeak;
import constraints.hard.global.AllDifferentPermutation;
import constraints.hard.global.AllDifferentWeak;
import constraints.hard.global.AllEqual;
import constraints.hard.global.Among;
import constraints.hard.global.CardinalityConstant;
import constraints.hard.global.Circuit;
import constraints.hard.global.Count.AtLeast1;
import constraints.hard.global.Count.AtLeastK;
import constraints.hard.global.Count.AtMost1;
import constraints.hard.global.Count.AtMostK;
import constraints.hard.global.Count.Exactly1;
import constraints.hard.global.Count.ExactlyK;
import constraints.hard.global.Cumulative;
import constraints.hard.global.Element.ElementConstant;
import constraints.hard.global.Element.ElementVariable;
import constraints.hard.global.ElementMatrix;
import constraints.hard.global.ExactlyKVariable;
import constraints.hard.global.Extremum.ExtremumCst;
import constraints.hard.global.Extremum.ExtremumCst.MaximumCst.MaximumCstGE;
import constraints.hard.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.hard.global.Extremum.ExtremumCst.MinimumCst.MinimumCstGE;
import constraints.hard.global.Extremum.ExtremumCst.MinimumCst.MinimumCstLE;
import constraints.hard.global.Extremum.ExtremumVar.Maximum;
import constraints.hard.global.Extremum.ExtremumVar.Minimum;
import constraints.hard.global.HammingProximityConstant.HammingProximityConstantGE;
import constraints.hard.global.HammingProximityConstant.HammingProximityConstantSumLE;
import constraints.hard.global.Lexicographic;
import constraints.hard.global.NValues;
import constraints.hard.global.NValues.NValuesGE;
import constraints.hard.global.NValues.NValuesLE;
import constraints.hard.global.NValuesVar;
import constraints.hard.global.NotAllEqual;
import constraints.hard.global.ObjVar;
import constraints.hard.global.ObjVar.ObjVarGE;
import constraints.hard.global.ObjVar.ObjVarLE;
import constraints.hard.global.SumScalarBoolean.SumScalarBooleanCst;
import constraints.hard.global.SumScalarBoolean.SumScalarBooleanVar;
import constraints.hard.global.SumSimple;
import constraints.hard.global.SumSimple.SumSimpleGE;
import constraints.hard.global.SumSimple.SumSimpleLE;
import constraints.hard.global.SumWeighted;
import constraints.hard.global.SumWeighted.SumWeightedGE;
import constraints.hard.global.SumWeighted.SumWeightedLE;
import constraints.hard.primitive.CtrPrimitiveBinary.CtrPrimitiveBinarySub;
import constraints.hard.primitive.CtrPrimitiveBinary.CtrPrimitiveBinarySub.SubNE2;
import constraints.hard.primitive.CtrPrimitiveBinary.Disjonctive;
import dashboard.ControlPanel.SettingVars;
import dashboard.Output;
import executables.Resolution;
import heuristics.values.HeuristicValues;
import heuristics.values.HeuristicValuesDirect.First;
import heuristics.values.HeuristicValuesDirect.Last;
import heuristics.values.HeuristicValuesDirect.Values;
import interfaces.ObserverConstruction;
import interfaces.ObserverDomainReduction;
import interfaces.OptimizationCompatible;
import objectives.OptimizationPilot;
import objectives.OptimizationPilot.OptimizationPilotBasic;
import objectives.OptimizationPilot.OptimizationPilotDecreasing;
import objectives.OptimizationPilot.OptimizationPilotDichotomic;
import objectives.OptimizationPilot.OptimizationPilotIncreasing;
import problems.ProblemFile;
import propagation.order1.PropagationForward;
import search.Solver;
import utility.Enums.EExportMode;
import utility.Kit;
import utility.Reflector;
import utility.exceptions.MissingImplementationException;
import variables.Variable;
import variables.VariableInteger;
import variables.VariableSymbolic;
import variables.domains.Domain;

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
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * scp[i].dom.highestValueDistance(), scp[i]);
		else {
			for (int i = 0; i < LIM; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * scp[i].dom.highestValueDistance(), scp[i]);
			for (int i = 0; i < LIM; i++)
				terms[LIM + i] = new Term((coeffs == null ? 1 : coeffs[scp.length - 1 - i]) * scp[scp.length - 1 - i].dom.highestValueDistance(),
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
	public void onConstructionProblemFinished() {
		Kit.control(Variable.areNumsNormalized(variables) && Constraint.areNumsNormalized(constraints), () -> "Non normalized nums in the problem");
		for (Variable x : variables) {
			x.dom.finalizeConstructionWith(variables.length + 1);
			Kit.control(Stream.of(x.ctrs).noneMatch(c -> c.num == -1), () -> "Pb with a non posted constraint ");
		}
		Set<String> allIds = new HashSet<>();
		for (Variable x : variables) {
			String name = x.id();
			Kit.control(!allIds.contains(name));
			allIds.add(name);
		}
		Kit.control((framework == TypeFramework.COP) == (optimizationPilot != null), () -> "Not a COP " + framework + " " + (optimizationPilot == null));
		if (rs.cp.settingExperimental.save4Baudouin)
			Stream.of(constraints).forEach(c -> ((CtrHard) c).save4Baudouin());
		if (priorityVars.length == 0 && annotations.decision != null)
			priorityVars = (Variable[]) annotations.decision;

		boolean strong = false;

		if (framework == TypeFramework.COP && rs.cp.settingValh.optValHeuristic) {
			Constraint c = ((Constraint) optimizationPilot.ctr);
			if (c instanceof ObjVar) {
				Variable x = c.scp[0];
				x.heuristicVal = optimizationPilot.minimization ? new First(x, false) : new Last(x, false);
				this.priorityVars = new Variable[] { x };
			} else if (c instanceof ExtremumCst) {
				if (strong)
					for (Variable x : c.scp)
						x.heuristicVal = optimizationPilot.minimization ? new First(x, false) : new Last(x, false); // the boolean is dummy
			} else if (c instanceof NValues) {
				assert c instanceof NValuesLE;
				if (strong)
					for (Variable x : c.scp)
						x.heuristicVal = new Values(x, false, c.scp);
			} else if (c instanceof SumWeighted) { // || c instanceof SumSimple) {
				int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
				Variable[] scp = prioritySumVars(c.scp, coeffs);
				if (scp != null) {
					for (Variable x : scp) {
						int coeff = c instanceof SumSimple ? 1 : coeffs[c.positionOf(x)];
						boolean f = optimizationPilot.minimization && coeff >= 0 || !optimizationPilot.minimization && coeff < 0;
						System.out.println("before " + x + " " + x.heuristicVal);
						x.heuristicVal = f ? new First(x, false) : new Last(x, false); // the boolean is dummy
						System.out.println("after " + x.heuristicVal);
					}
					this.priorityVars = scp;
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
	}

	@Override
	public void onConstructionSolverFinished() {
		Stream.of(variables).forEach(x -> x.dom.setSolver(solver));
	}

	// ************************************************************************
	// ***** Fields
	// ************************************************************************

	public final Resolution rs;

	/**
	 * The kind of problem, i.e. the framework (CSP, COP, WCSP, ...) to which it belongs. Alias for resolution.cfg.framework.
	 */
	public TypeFramework framework;

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

	/** The objective of the problem. Maybe null. */
	public OptimizationPilot optimizationPilot;

	/**
	 * The priority variables. For example, those that have to be assigned in priority by a backtrack search solver. There is 0 priority variable by
	 * default.
	 */
	public Variable[] priorityVars = new Variable[0];

	/**
	 * The priority variables put in the array above at indices ranging from 0 to this field value should be assigned strictly in that order.
	 */
	public int nStrictPriorityVars;

	/**
	 * An object used to record many data corresponding to metrics and various features of the problem.
	 */
	public ProblemStuff stuff; // = new ProblemStuff(this);

	/**
	 * The object used to manage symbolic values. Basically, it transforms symbols into integers, but this is not visible for the user (modeler).
	 */
	public Symbolic symbolic;

	public int nTuplesRemoved;

	public int nValuesRemoved; // sum over all variable domains

	/**
	 * The list of generators of an identified symmetry group of variables. Maybe, empty.
	 */
	public final List<List<int[]>> symmetryGroupGenerators = new ArrayList<>();

	/**
	 * The list of observers on domains. Whenever a domain is reduced, a callback function is called.
	 */
	public final Collection<ObserverDomainReduction> observersDomainReduction = new ArrayList<>();

	// ************************************************************************
	// ***** Parameters
	// ************************************************************************

	@Override
	public final String name() {
		String s = super.name();
		return s.matches("XCSP[23]-.*") ? s.substring(6)
				: s.startsWith(ProblemFile.class.getSimpleName()) ? s.substring(ProblemFile.class.getSimpleName().length() + 1) : s;
	}

	/**
	 * This method can be used for modifying the value of a parameter. This is an advanced tool for handling series of instances.
	 */
	public final void modifyAskedParameter(int index, Object value) {
		parameters.set(index, new SimpleEntry<>(value, parameters.get(index).getValue()));
	}

	public int askInt(String message, Predicate<Integer> control, IntFunction<String> format, boolean incrementWhenSeries) {
		Integer v = Utilities.toInteger(ask(message));
		Utilities.control(v != null, "Value " + v + " for " + message + " is not valid (not an integer)");
		v += (incrementWhenSeries ? rs.instanceNumber : 0);
		Utilities.control(control == null || control.test(v), "Value " + v + " for " + message + " does not respect the control " + control);
		return (Integer) addParameter(v, format == null ? null : format.apply(v));
	}

	public int askInt(String message, Predicate<Integer> control, String format, boolean incrementWhenSeries) {
		return askInt(message, control, v -> format, incrementWhenSeries);
	}

	public int askInt(String message, Predicate<Integer> control, boolean incrementWhenSeries) {
		return askInt(message, control, (IntFunction<String>) null, incrementWhenSeries);
	}

	public int askInt(String message, String format, boolean incrementWhenSeries) {
		return askInt(message, null, format, incrementWhenSeries);
	}

	public int askInt(String message, boolean incrementWhenSeries) {
		return askInt(message, null, (IntFunction<String>) null, incrementWhenSeries);
	}

	public final Var[][] project3(Var[][][] m) {
		return IntStream.range(0, m[0][0].length).mapToObj(i -> api.select(m, (w, g, p) -> p == i)).toArray(Var[][]::new);
	}

	// public final void removeVariable(Variable var) {
	// collectedVariables.remove(var); collectedConstraints.remove(var.ctrs);
	// storeVariablesToArray(); storeConstraintsToArray(); }

	/**
	 * 
	 * /** Removes a constraint that has already been built. Should not be called when modeling. Advanced use.
	 */
	public void removeCtr(Constraint c) {
		// System.out.println("removed " + c + "size=" + stuff.collectedCtrsAtInit.size());
		Kit.control(constraints == null, () -> "too late");
		stuff.collectedCtrsAtInit.remove(c);
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
		if (stuff.collectedCtrsAtInit.isEmpty()) // first call
			System.out.println("\n" + Output.COMMENT_PREFIX + "Loading constraints...");
		if (rs.cp.verbose > 1 && !rs.cp.settingXml.competitionMode) {
			int n = stuff.collectedCtrsAtInit.size(), nDigits = (int) Math.log10(n) + 1;
			IntStream.range(0, nDigits).forEach(i -> System.out.print("\b"));
			System.out.print((n + 1) + "");
		}

		c.num = stuff.addCollectedConstraint(c);
		// System.out.println("adding " + c);
		return ctrEntities.new CtrAlone(c, classes);
	}

	public void annotateVarhStatic(Variable[] vars) {
		if (rs.cp.settingGeneral.enableAnnotations) {
			priorityVars = vars;
			nStrictPriorityVars = priorityVars.length;
		}
	}

	public void annotateValh(Var[] vars, Class<? extends HeuristicValues> clazz) {
		if (rs.cp.settingGeneral.enableAnnotations) {
			Stream.of(vars)
					.forEach(x -> ((Variable) x).heuristicVal = Reflector.buildObject(clazz.getSimpleName(), HeuristicValues.class, new Object[] { x, null }));
		}
	}

	/**
	 * Method that resets the problem instance. Each variable and each constraint is reset. The specified Boolean parameter indicates whether the
	 * weighted degrees values must not be reset or not.
	 */
	public void reset() {
		Stream.of(variables).forEach(x -> x.reset());
		Stream.of(constraints).forEach(c -> c.reset());
		Stream.of(constraints).forEach(c -> c.ignored = false);
		// stuff = new ProblemStuff(this); // TODO reset or building a new object ?
		nTuplesRemoved = nValuesRemoved = 0;
		if (rs.cp.verbose > 0)
			Kit.log.info("Reset of problem instance");
	}

	public void reduceTo(boolean[] presentVariables, boolean[] presentConstraints) {
		Kit.control(symmetryGroupGenerators.size() == 0 && presentVariables.length == variables.length && presentConstraints.length == constraints.length);
		assert Variable.firstWipeoutVariableIn(variables) == null && Variable.areNumsNormalized(variables) && Constraint.areNumsNormalized(constraints);
		priorityVars = IntStream.range(0, variables.length).filter(i -> presentVariables[i]).mapToObj(i -> variables[i]).toArray(Variable[]::new);
		for (Variable x : priorityVars)
			x.reset();
		for (int i = 0; i < constraints.length; i++)
			if (!(constraints[i].ignored = !presentConstraints[i]))
				constraints[i].reset();
		// stuff = new ProblemStuff(this); // TODO reset or building a new
		// object ?
		nTuplesRemoved = nValuesRemoved = 0;
		if (rs.cp.verbose >= 0)
			Kit.log.info("Reduction to (#V=" + priorityVars.length + ",#C=" + Kit.countIn(true, presentConstraints) + ")");
	}

	private CtrAlone buildCtrTrue(Variable x, Variable y) {
		return ((CtrAlone) (x instanceof VariableInteger ? api.ctrTrue(new VariableInteger[] { (VariableInteger) x, (VariableInteger) y })
				: api.ctrTrue(new VariableSymbolic[] { (VariableSymbolic) x, (VariableSymbolic) y })));
	}

	public final Constraint addUniversalConstraintDynamicallyBetween(Variable x, Variable y) {
		assert x.getClass() == y.getClass();
		assert !Stream.of(y.ctrs).anyMatch(c -> c.scp.length == 2 && c.involves(x));
		assert solver.propagation instanceof PropagationForward;

		CtrAlone ca = extension(vars(x, y), new int[0][], false, DONT_KNOW);
		Constraint c = (Constraint) ca.ctr; // (Constraint) buildCtrTrue(x, y).ctr;
		c.cloneStructures(false);
		constraints = stuff.collectedCtrsAtInit.toArray(new Constraint[stuff.collectedCtrsAtInit.size()]); // storeConstraintsToArray();
		x.whenFinishedProblemConstruction();
		y.whenFinishedProblemConstruction();
		// constraint.buildBitRmResidues();
		if (x.isAssigned())
			c.doPastVariable(x);
		if (y.isAssigned())
			c.doPastVariable(y);
		return c;
	}

	private void makeGraphComplete() {
		if (rs.cp.settingProblem.completeGraph) {
			int sizeBefore = stuff.collectedCtrsAtInit.size();
			// TODO : improve the complexity of finding missing binary constraints below
			IntStream.range(0, variables.length).forEach(i -> IntStream.range(i + 1, variables.length).forEach(j -> {
				if (!stuff.collectedCtrsAtInit.stream().anyMatch(c -> c.scp.length == 2 && c.involves(variables[i], variables[j])))
					buildCtrTrue(variables[i], variables[j]);
			}));
			stuff.nAddedCtrs += stuff.collectedCtrsAtInit.size() - sizeBefore;
		}
	}

	private void buildSymmetries() {
		if (rs.cp.settingProblem.isSymmetryBreaking()) {
			int nBefore = stuff.collectedCtrsAtInit.size();
			for (Constraint c : stuff.collectedCtrsAtInit)
				if (Constraint.getSymmetryMatching(c.key) == null)
					Constraint.putSymmetryMatching(c.key, c.defineSymmetryMatching());
			IdentificationAutomorphism automorphismIdentification = new IdentificationAutomorphism(this);
			for (Constraint c : automorphismIdentification.buildVariableSymmetriesFor(variables, stuff.collectedCtrsAtInit))
				addCtr(c);
			stuff.addToMapForAutomorphismIdentification(automorphismIdentification);
			symmetryGroupGenerators.addAll(automorphismIdentification.getGenerators());
			stuff.nAddedCtrs += stuff.collectedCtrsAtInit.size() - nBefore;
		}
	}

	private void inferAllDifferents() {
		if (rs.cp.settingCtrs.inferAllDifferentNb > 0)
			stuff.addToMapForAllDifferentIdentification(new IdentificationAllDifferent(this));
	}

	/**
	 * This method is called when the initialization is finished in order to, among other things, put constraints into an array.
	 */
	public final void storeConstraintsToArray() {
		makeGraphComplete();
		buildSymmetries();
		inferAllDifferents();
		constraints = stuff.collectedCtrsAtInit.toArray(new Constraint[0]);
		for (Variable var : variables) {
			var.whenFinishedProblemConstruction();
			stuff.varDegrees.add(var.deg());
		}
		assert Variable.areNumsNormalized(variables);// && Constraint.areIdsNormalized(constraints); TODO
		rs.clearMapsUsedByConstraints();
	}

	public Variable findVarWithNumOrId(Object o) {
		if (o instanceof Integer) {
			int num = (Integer) o;
			Kit.control(0 <= num && num < variables.length, () -> num + " is not a valid variable num. Check your configuration parameters -ins -pr1 or -pr2.");
			Kit.control(variables[num].num != Variable.UNSET_NUM,
					() -> "You cannot use the discarded variable whose (initial) num is " + num + ". Check your configuration parameters -ins -pr1 or -pr2.");
			return variables[num];
		} else {
			Variable var = mapForVars.get(o);
			Kit.control(var != null, () -> "The variable " + o + " cannot be found. Check your configuration parameters -ins -pr1 or -pr2.");
			Kit.control(var.num != Variable.UNSET_NUM,
					() -> "You cannot use the discarded variable " + o + ". Check your configuration parameters. -ins -pr1 or -pr2.");
			return var;
		}
	}

	private final void addUnaryConstraintsOfUserInstantiation() {
		SettingVars settings = rs.cp.settingVars;
		Kit.control(settings.instantiatedVars.length == settings.instantiatedVals.length,
				() -> "In the given instantiation, the number of variables (ids or names) is different from the number of values.");
		boolean removeValues = true; // hard coding TODO
		for (int i = 0; i < settings.instantiatedVars.length; i++) {
			Variable x = findVarWithNumOrId(settings.instantiatedVars[i]);
			int v = settings.instantiatedVals[i];
			Kit.control(x.dom.toPresentIdx(v) != -1, () -> "Value " + v + " not present in domain of " + x + ". Check  -ins.");
			if (removeValues)
				x.dom.reduceToValueAtConstructionTime(v);
			else
				equal(x, v);
		}
	}

	private final void reduceDomainsOfIsolatedVariables() {
		// TODO other frameworks ?
		boolean reduceIsolatedVars = rs.cp.settingVars.reduceIsolatedVars && rs.cp.settingGeneral.nSearchedSolutions == 1
				&& !rs.cp.settingProblem.isSymmetryBreaking() && rs.cp.settingGeneral.framework == TypeFramework.CSP;
		List<Variable> isolatedVars = new ArrayList<>(), fixedVars = new ArrayList<>();
		int nRemovedValues = 0;
		for (Variable x : stuff.collectedVarsAtInit) {
			if (x.ctrs.length == 0) {
				isolatedVars.add(x);
				if (reduceIsolatedVars) {
					nRemovedValues += x.dom.size() - 1;
					x.dom.reduceToValueAtConstructionTime(x.dom.firstValue());
				}
			}
			if (x.dom.size() == 1)
				fixedVars.add(x);
		}
		if (isolatedVars.size() > 0) {
			stuff.nIsolatedVars += isolatedVars.size();
			Kit.log.info("Isolated variables : " + Kit.join(isolatedVars));
			Kit.log.info("Nb values removed due to isolated variables : " + nRemovedValues + "\n");
		}
		if (fixedVars.size() > 0) {
			stuff.nFixedVars += fixedVars.size();
			Kit.log.info("Fixed variables : " + (fixedVars.size() <= 100 ? Kit.join(fixedVars) : "more than 100") + "\n");
		}
	}

	private final void updateConflictsStructuresIfReducedDomains() {
		if (nValuesRemoved > 0) {
			// Kit.warning(true, Domain.getNbValuesRemoved() +" values removed
			// by unary constraints and reduceDomainsOfIsolatedVariables ");
			int[] domainFrontiers = Kit.repeat(-1, variables.length);
			for (Constraint ctr : constraints)
				if (ctr instanceof CtrHard)
					((CtrHard) ctr).updateConflictsStructures(domainFrontiers);
		}
	}

	public static int[][] buildTable(Variable[] scp, CtrHard... ctrs) {
		// Var[] scp = distinct(vars(Stream.of(ctrs).map(c -> c.scp).toArray()));
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

	public int[][] buildTable(CtrHard... ctrs) {
		return buildTable(distinctSorted(vars(Stream.of(ctrs).map(c -> c.scp).toArray())), ctrs);
	}

	public Problem(ProblemAPI api, String modelVariant, String data, String dataFormat, boolean dataSaving, String[] argsForPb, Resolution rs) {
		super(api, modelVariant, argsForPb);
		this.rs = rs;
		rs.problem = this; // required because needed during initialization of some objects
		rs.observersConstruction.add(0, this); // "Must be the first in the list when calling onConstructionSolverFinished
		// Kit.control(rs.observersConstructionSolver.size() == 0, () -> "Must be the first in the list " + rs.observersConstructionSolver.size());
		// rs.observersConstructionSolver.add(this);
		this.framework = rs.cp.settingGeneral.framework;
		this.stuff = new ProblemStuff(this);
		this.rs.output.beforeData();
		loadData(data, dataFormat, dataSaving);
		this.rs.output.afterData();
		api.model();

		// storeVariablesToArray();
		// fixNamesOfVariables();
		variables = stuff.collectedVarsAtInit.toArray(new Variable[stuff.collectedVarsAtInit.size()]);
		addUnaryConstraintsOfUserInstantiation();
		storeConstraintsToArray();
		// currently, only mono-objective optimization supported
		if (Solver.class.getSimpleName().equals(rs.cp.settingSolving.clazz))
			optimizationPilot = new OptimizationPilotBasic(this, "#violatedConstraints");

		reduceDomainsOfIsolatedVariables();
		updateConflictsStructuresIfReducedDomains();
	}

	public final void display() {
		if (rs.cp.verbose >= 2) {
			log.finer("\nProblem " + name());
			Stream.of(variables).forEach(x -> x.display(rs.cp.verbose == 3));
			Stream.of(constraints).forEach(c -> c.display(rs.cp.verbose == 3));
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
		return framework;
	}

	/**
	 * Adds a variable that has already be built. Should not be called directly when modeling.
	 */
	public final Variable addVar(Variable x) {
		Kit.control(!mapForVars.containsKey(x.id()), () -> x.id() + " duplicated");
		if (stuff.mustDiscard(x))
			return null;
		if (stuff.collectedVarsAtInit.isEmpty())
			System.out.print(Output.COMMENT_PREFIX + "Loading variables...\n");
		if (rs.cp.verbose > 1 && !rs.cp.settingXml.competitionMode) {
			int n = stuff.collectedVarsAtInit.size(), nDigits = n < 10 ? 1 : n < 100 ? 2 : n < 1000 ? 3 : n < 10000 ? 4 : n < 100000 ? 5 : n < 1000000 ? 6 : 7;
			IntStream.range(0, nDigits).forEach(i -> System.out.print("\b"));
			System.out.print((n + 1) + "");
		}
		x.num = stuff.addCollectedVariable(x);
		mapForVars.put(x.id(), x);
		return x;
	}

	@Override
	public VariableInteger buildVarInteger(String id, Dom dom) {
		Object[] values = dom.values;
		VariableInteger x = null;
		if (values.length == 1 && values[0] instanceof IntegerInterval) {
			IntegerInterval ii = (IntegerInterval) values[0];
			int min = Utilities.safeIntWhileHandlingInfinity(ii.inf), max = Utilities.safeIntWhileHandlingInfinity(ii.sup);
			x = new VariableInteger(this, id, min, max);
		} else if (values.length == 3 && values[0] instanceof IntegerValue && values[1] instanceof IntegerValue && values[2] instanceof IntegerValue
				&& ((IntegerValue) values[2]).v == Domain.TAG_RANGE) { // necessary for XCSP2 instances
			x = new VariableInteger(this, id, Utilities.safeIntWhileHandlingInfinity(((IntegerValue) values[0]).v),
					Utilities.safeIntWhileHandlingInfinity(((IntegerValue) values[1]).v));
		} else {
			// TODO use a cache here to avoid building the array of values several times
			x = new VariableInteger(this, id, IntegerEntity.toIntArray((IntegerEntity[]) values, Integer.MAX_VALUE));
		}
		return (VariableInteger) addVar(x);
	}

	@Override
	public VariableSymbolic buildVarSymbolic(String id, DomSymbolic dom) {
		return (VariableSymbolic) addVar(new VariableSymbolic(this, id, (String[]) dom.values));
	}

	// public final CtrAlone addCtr(Constraint c, TypeClass... classes) {
	// return ui.addCtr(c, classes);
	// }

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

	private Variable[] translate(IVar[] t) {
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

	// ************************************************************************
	// ***** Constraint intension
	// ************************************************************************

	@Override
	public final CtrAlone intension(XNodeParent<IVar> tree) {
		Variable[] scp = (Variable[]) tree.vars();
		assert Stream.of(scp).allMatch(x -> x instanceof Var) || Stream.of(scp).allMatch(x -> x instanceof VarSymbolic);
		if (scp.length == 1 && !rs.mustPreserveUnaryConstraints()) {
			Variable x = scp[0];
			TreeEvaluator evaluator = x instanceof VariableInteger ? new TreeEvaluator(tree) : new TreeEvaluator(tree, symbolic.mapOfSymbols);
			x.dom.executeOnValues(v -> {
				if (evaluator.evaluate(v) != 1)
					x.dom.removeValueAtConstructionTime(v);
			});
			stuff.nRemovedUnaryCtrs++;
			return ctrEntities.new CtrAloneDummy("Removed unary constraint by domain reduction");
		}
		// System.out.println("kkkk" + Variable.nValidTuplesBoundedAtMaxValueFor(scp));
		if (scp.length <= rs.cp.settingExtension.arityLimitForIntensionToExtension
				&& Variable.nValidTuplesBoundedAtMaxValueFor(scp) <= rs.cp.settingExtension.validLimitForIntensionToExtension
				&& Stream.of(scp).allMatch(x -> x instanceof Var)) {
			stuff.nConvertedConstraints++;
			return extension(tree);
		}

		// System.out.println(tree);
		// tree = (XNodeParent<IVar>) tree.canonization();
		// if (ConstraintRecognizer.x_ariop_y__relop_z.matches(tree)) {
		// if (tree.ariop(0) == DIST && tree.relop(0) == EQ)
		// return CtrPrimitiveTernaryDist.buildFrom(this, (Variable) tree.var(0), (Variable) tree.var(1), EQ, (Variable) tree.var(2));
		// }

		// System.out.println("hhhhh " + tree);

		return addCtr(new CtrIntension(this, scp, tree));
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

	public final CtrAlone extension(IVar[] scp, Object tuples, boolean positive, Boolean starred) {
		return addCtr(CtrExtension.build(this, translate(scp), tuples, positive, starred));
	}

	@Override
	public final CtrAlone extension(Var[] scp, int[][] tuples, boolean positive) {
		if (tuples.length == 0)
			return addCtr(positive ? new CtrHardFalse(this, translate(scp), "Table constraint with 0 support") : new CtrHardTrue(this, translate(scp)));
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
	// ***** Constraint regular
	// ************************************************************************

	@Override
	public final CtrAlone regular(Var[] list, Automaton automaton) {
		return addCtr(new CtrExtensionMDD(this, translate(list), automaton));
	}

	// ************************************************************************
	// ***** Constraint mdd
	// ************************************************************************

	@Override
	public final CtrAlone mdd(Var[] list, Transition[] transitions) {
		return addCtr(new CtrExtensionMDD(this, translate(list), transitions));
	}

	public final CtrAlone mdd(Var[] scp, int[][] tuples) {
		return addCtr(new CtrExtensionMDD(this, translate(scp), tuples));
	}

	public final CtrAlone mddOr(Var[] scp, MDDCD[] t) {
		return addCtr(new CtrExtensionOrMDD(this, translate(scp), t));
	}

	// ************************************************************************
	// ***** Constraint allDifferent
	// ************************************************************************

	private CtrEntity allDifferent(Variable[] scp) {
		if (scp.length <= 1)
			return ctrEntities.new CtrAloneDummy("Removed alldiff constraint with scope length = " + scp.length);
		if (isBasicType(rs.cp.settingGlobal.typeAllDifferent))
			return addCtr(Variable.isPermutationElligible(scp) ? new AllDifferentPermutation(this, scp) : new AllDifferent(this, scp));
		if (rs.cp.settingGlobal.typeAllDifferent == 1)
			return forall(range(scp.length).range(scp.length), (i, j) -> {
				if (i < j)
					addCtr(new SubNE2(this, scp[i], scp[j], 0)); // different(scp[i], scp[j]);
			});
		if (rs.cp.settingGlobal.typeAllDifferent == 2)
			return addCtr(new AllDifferentWeak(this, scp));
		if (rs.cp.settingGlobal.typeAllDifferent == 3)
			return addCtr(new AllDifferentCounting(this, scp));
		if (rs.cp.settingGlobal.typeAllDifferent == 4)
			return addCtr(new AllDifferentBound(this, scp));
		throw new MissingImplementationException();
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
		Kit.control(exceptValues.length >= 1);
		if (rs.cp.settingGlobal.typeAllDifferent <= 1)
			return forall(range(scp.length).range(scp.length), (i, j) -> {
				if (i < j)
					intension(or(ne(scp[i], scp[j]), exceptValues.length == 1 ? eq(scp[i], exceptValues[0]) : in(scp[i], exceptValues)));
			});
		if (rs.cp.settingGlobal.typeAllDifferent == 2)
			return addCtr(new AllDifferentExceptWeak(this, translate(scp), exceptValues));
		throw new MissingImplementationException();
	}

	private CtrAlone distinctVectors(Variable[] t1, Variable[] t2) {
		Kit.control(Variable.areAllDistinct(vars(t1, t2)), () -> "For the moment not handled");
		if (isBasicType(rs.cp.settingGlobal.typeDistinctVectors2))
			return addCtr(CtrExtensionSmart.buildDistinctVectors(this, t1, t2)); // return addCtr(new DistinctVectors2(this, t1, t2)); // BUG TO BE
																					// FIXED
		if (rs.cp.settingGlobal.typeDistinctVectors2 == 1) {
			if (rs.cp.settingGlobal.smartTable)
				return addCtr(CtrExtensionSmart.buildDistinctVectors(this, t1, t2));
			if (rs.cp.settingGlobal.jokerTable)
				return extension(vars(t1, t2), Table.shortTuplesFordNotEqualVectors(t1, t2), true);
		}
		throw new MissingImplementationException();
	}

	/**
	 * Builds a DistinctVectors constraint. The tuple of values corresponding to the assignment of the variables in the array specified as first
	 * parameter must be different from the tuple of values corresponding to the assignment of the variables in the array specified as second
	 * parameter.
	 */
	private CtrEntity distinctVectors(Variable[][] lists) {
		if (rs.cp.settingGlobal.typeDistinctVectorsK == 1)
			return forall(range(lists.length).range(lists.length), (i, j) -> {
				if (i < j) {
					if (rs.cp.settingGlobal.smartTable)
						addCtr(CtrExtensionSmart.buildDistinctVectors(this, lists[i], lists[j]));
					else if (rs.cp.settingGlobal.jokerTable)
						extension(vars(lists[i], lists[j]), Table.shortTuplesFordNotEqualVectors(lists[i], lists[j]), true);
					else
						addCtr(CtrExtensionSmart.buildDistinctVectors(this, lists[i], lists[j])); // addCtr(new DistinctVectors2(this,
																									// lists[i], lists[j])); // BUG TO BE
																									// FIXED
				}
			});
		throw new MissingImplementationException();
	}

	@Override
	public final CtrEntity allDifferentList(Var[]... lists) {
		Kit.control(lists.length >= 2);
		Variable[][] m = translate2D(lists);
		return lists.length == 2 ? distinctVectors(m[0], m[1]) : distinctVectors(m);
	}

	@Override
	public final CtrEntity allDifferentMatrix(Var[][] matrix) {
		if (isBasicType(rs.cp.settingGlobal.typeAllDifferentMatrix))
			return addCtr(RawAllDifferent.buildFrom(this, vars(matrix), MATRIX, varEntities.compactMatrix(matrix), null));
		if (rs.cp.settingGlobal.typeAllDifferentMatrix == 1) {
			CtrArray ctrSet1 = forall(range(matrix.length), i -> allDifferent(matrix[i]));
			CtrArray ctrSet2 = forall(range(matrix[0].length), i -> allDifferent(api.columnOf(matrix, i)));
			return ctrSet1.append(ctrSet2);
		}
		throw new MissingImplementationException();
	}

	@Override
	public CtrEntity allDifferent(XNode<IVar>[] trees) {
		Var[] aux = replaceByVariables(trees);
		return allDifferent(aux);
		// return forall(range(trees.length).range(trees.length), (i, j) -> {
		// if (i < j)
		// different(trees[i], trees[j]);
		// });
	}

	// ************************************************************************
	// ***** Constraint allEqual
	// ************************************************************************

	private int[][] allEqualTable(Variable[] scp) {
		List<int[]> table = new ArrayList<>();
		for (int a = scp[0].dom.first(); a != -1; a = scp[0].dom.next(a)) {
			int v = scp[0].dom.toVal(a);
			boolean support = true;
			for (int i = 1; support && i < scp.length; i++)
				if (!scp[i].dom.isPresentValue(v))
					support = false;
			if (support)
				table.add(Kit.repeat(v, scp.length));
		}
		return table.toArray(new int[0][]);
	}

	// private CtrEntity allEqualtt(Var[] list) {
	// Variable[] scp = translate(list);
	// List<int[]> table = new ArrayList<>();
	// for (int a = scp[0].dom.first(); a != -1; a = scp[0].dom.next(a)) {
	// int v = scp[0].dom.toVal(a);
	// boolean support = true;
	// for (int i = 1; support && i < scp.length; i++)
	// if (!scp[i].dom.isPresentValue(v))
	// support = false;
	// if (support)
	// table.add(Kit.repeat(v, scp.length));
	// }
	// return extension(list, table.toArray(new int[0][]), true);
	// ;
	// if (isBasicType(rs.cp.global.typeAllEqual))
	// return addCtr(new AllEqual(this, scp));
	// if (rs.cp.global.typeAllEqual == 1)
	// return forall(range(scp.length - 1), i -> equal(scp[i], scp[i + 1]));
	// if (rs.cp.global.typeAllEqual == 2) {
	// if (rs.cp.global.smartTable)
	// return addCtr(CtrExtensionSmart.buildAllEqual(this, scp));
	// if (rs.cp.global.basicTable) {
	// // efficiency not a big deal here
	// int[][] tuples = IntStream.of(scp[0].dom.currValues()).mapToObj(val -> Kit.repeat(val, scp.length)).toArray(int[][]::new);
	// return api.extension((VariableInteger[]) scp, Variable.filterTuples(scp, tuples, false));
	// }
	// }
	// throw new MissingImplementationException();
	// }

	@Override
	public final CtrEntity allEqual(Var... scp) {
		// return forall(range(scp.length - 1), i -> CtrPrimitiveBinaryAdd.buildFrom(this, (Variable) scp[i], 0, EQ, (Variable) scp[i + 1]));
		return addCtr(new AllEqual(this, translate(scp)));
		// return extension(scp, allEqualTable(translate(scp)), true, false);
	}

	@Override
	public final CtrEntity allEqual(VarSymbolic... scp) {
		throw new MissingImplementationException();
	}

	@Override
	public final CtrEntity allEqualList(Var[]... lists) {
		control(lists.length >= 2);
		throw new MissingImplementationException();
	}

	// ************************************************************************
	// ***** Constraint ordered/lexicographic
	// ************************************************************************

	/**
	 * Ensures that the specified array of variables is ordered according to the specified operator, when considering the associated lengths. We must
	 * have x[i]+lengths[i] op x[i+1]. Can be decomposed into a sequence of binary constraints.
	 */
	@Override
	public final CtrEntity ordered(Var[] list, int[] lengths, TypeOperatorRel op) {
		control(list != null && lengths != null && list.length == lengths.length + 1 && op != null);
		TypeConditionOperatorRel cop = op.toConditionOperator();
		return forall(range(list.length - 1), i -> CtrPrimitiveBinarySub.buildFrom(this, (Variable) list[i], (Variable) list[i + 1], cop, -lengths[i]));
	}

	/**
	 * Ensures that the specified array of variables is ordered according to the specified operator, when considering the associated lengths. We must
	 * have list[i]+lengths[i] op list[i+1]. Can be decomposed into a sequence of binary constraints.
	 */
	@Override
	public final CtrEntity ordered(Var[] list, Var[] lengths, TypeOperatorRel op) {
		control(list != null && lengths != null && list.length == lengths.length + 1 && op != null);
		return forall(range(list.length - 1), i -> intension(XNodeParent.build(op.toExpr(), add(list[i], lengths[i]), list[i + 1]))); // TODO
																																		// extension ?
																																		// via
																																		// primitive ?
	}

	/**
	 * Builds and returns a Lexicographic constraint. The tuple of values corresponding to the assignment of the variables in the array specified as
	 * first parameter must be before the tuple of values corresponding to the assignment of the variables in the array specified as second parameter.
	 * The meaning of the relation "before" is given by the value of the specified operator that must be one value among LT, LE, GT, and GE.
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

	private String idAux() {
		return AUXILIARY_VARIABLE_PREFIX + varEntities.allEntities.size();
	}

	public Variable replaceByVariable(XNode<IVar> tree) {
		// int[] values = tree.getType().isPredicateOperator() ? new int[] { 0, 1 } : new
		// EvaluationManager(tree).generatePossibleValues(Variable.initDomainValues(vars(tree)));

		Object values = tree.possibleValues();
		Dom dom = values instanceof Range ? api.dom((Range) values) : api.dom((int[]) values);
		Var aux = api.var(idAux(), dom, "auxiliary variable");
		if (Constraint.howManyVarsWithin(vars(tree), rs.cp.settingPropagation.spaceLimitation) == ALL) {
			int[][] tuples = new TreeEvaluator(tree).computeTuples(Variable.initDomainValues(vars(tree)));
			extension(vars(tree, aux), tuples, true); // extension(eq(aux, tree));
		} else
			equal(aux, tree);
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

	private Var[] replaceByVariables(XNode<IVar>[] trees) {
		IntToDom doms = i -> {
			Object values = trees[i].possibleValues();
			return values instanceof Range ? api.dom((Range) values) : api.dom((int[]) values);
		};
		if (trees.length > 1 && IntStream.range(1, trees.length).allMatch(i -> areSimilar(trees[0], trees[i]))) {
			Var[] aux = api.array(idAux(), api.size(trees.length), doms.apply(0), "auxiliary variables");
			int[][] tuples = Constraint.howManyVarsWithin(vars(trees[0]), rs.cp.settingPropagation.spaceLimitation) == ALL
					? new TreeEvaluator(trees[0]).computeTuples(Variable.initDomainValues(vars(trees[0])))
					: null;
			for (int i = 0; i < trees.length; i++) {
				if (tuples != null)
					extension(vars(trees[i], aux[i]), tuples, true); // extension(eq(aux[i], trees[i]));
				else
					equal(aux[i], trees[i]);
			}
			return aux;
		}

		Var[] aux = api.array(idAux(), api.size(trees.length), doms, "auxiliary variables");
		for (int i = 0; i < trees.length; i++) {
			if (Constraint.howManyVarsWithin(vars(trees[i]), rs.cp.settingPropagation.spaceLimitation) == ALL) {
				int[][] tuples = new TreeEvaluator(trees[i]).computeTuples(Variable.currDomainValues(vars(trees[i])));
				extension(vars(trees[i], aux[i]), tuples, true); // extension(eq(aux[i], trees[i]));
			} else
				equal(aux[i], trees[i]);
		}
		return aux;
	}

	private Var[] replaceByVariables(Stream<XNode<IVar>> trees) {
		return replaceByVariables(trees.toArray(XNode[]::new));
	}

	private CtrAlone sum(IVar[] vars, int[] coeffs, TypeConditionOperatorRel op, long limit, boolean inversable) {
		// we canonize terms (group together several occurrences of the same variables and discard terms of coefficient 0)
		Variable[] list = translate(vars);
		Term[] terms = new Term[list.length];
		for (int i = 0; i < terms.length; i++)
			terms[i] = new Term(coeffs == null ? 1 : coeffs[i], list[i]);
		if (!Variable.areAllDistinct(list)) {
			Set<Entry<Variable, Long>> entries = Stream.of(terms).collect(groupingBy(t -> t.var, summingLong((Term t) -> (int) t.coeff))).entrySet();
			terms = entries.stream().map(e -> new Term(e.getValue(), e.getKey())).toArray(Term[]::new);
			Kit.log.info("Sum constraint with several ocurrences of the same variable");
		}
		terms = Stream.of(terms).filter(t -> t.coeff != 0).sorted().toArray(Term[]::new); // we discard terms of coeff 0 and sort them
		list = Stream.of(terms).map(t -> t.var).toArray(Variable[]::new);
		Kit.control(Stream.of(terms).allMatch(t -> Utilities.isSafeInt(t.coeff)));
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
		return sum(list, coeffs, op, limit, true);
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
					return addCtr(new CtrExtensionMDD(this, translate(list), coeffs, rightTerm));
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
		Kit.control(list.length != 0 && k >= 0);
		Variable[] scp = Stream.of(list).filter(x -> ((VariableInteger) x).dom.isPresentValue(value) && ((VariableInteger) x).dom.size() > 1)
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
		Kit.control(k >= 0);
		Variable[] scp = Stream.of(list).filter(x -> ((VariableInteger) x).dom.isPresentValue(value) && ((VariableInteger) x).dom.size() > 1)
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
		Kit.control(list.length != 0 && k >= 0);
		Variable[] scp = Stream.of(list).filter(x -> ((VariableInteger) x).dom.isPresentValue(value) && ((VariableInteger) x).dom.size() > 1)
				.toArray(Variable[]::new);
		int newK = k - (int) Stream.of(list).filter(x -> ((VariableInteger) x).dom.onlyContainsValue(value)).count();
		Kit.control(newK >= 0, () -> "UNSAT, constraint Exactly with scope " + Kit.join(list) + " has already more than " + k + " variables equal to " + value);
		if (newK == 0)
			return forall(range(scp.length), i -> different(scp[i], value));
		if (newK == scp.length)
			return forall(range(scp.length), i -> equal(scp[i], value));
		Kit.control(newK < scp.length,
				() -> "Instance is UNSAT, constraint Exactly with scope " + Kit.join(list) + " cannot have " + k + " variables equal to " + value);
		return newK == 1 ? addCtr(new Exactly1(this, scp, value)) : addCtr(new ExactlyK(this, scp, value, newK));
	}

	private CtrEntity among(Var[] list, int[] values, int k) {
		Kit.control(list.length >= k);
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
				return addCtr(new ExactlyKVariable(this, list, values[0], limit));
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
				if (isBasicType(rs.cp.settingGlobal.typeNotAllEqual))
					return addCtr(new NotAllEqual(this, (VariableInteger[]) list));
				if (rs.cp.settingGlobal.typeNotAllEqual == 1) {
					VariableInteger[] clone = (VariableInteger[]) list.clone();
					return intension(or(IntStream.range(0, list.length - 1).mapToObj(i -> XNodeParent.ne(clone[i], clone[i + 1])).toArray(Object[]::new)));
				}
			}
			if (op == LE || op == LT)
				return addCtr(new NValuesLE(this, (VariableInteger[]) list, op == LE ? k : k - 1));
			if (op == GE || op == GT)
				return addCtr(new NValuesGE(this, (VariableInteger[]) list, op == GE ? k : k + 1));
		} else if (condition instanceof ConditionVar) {
			TypeConditionOperatorRel op = ((ConditionVar) condition).operator;
			if (op == EQ)
				return addCtr(new NValuesVar(this, (VariableInteger[]) list, (VariableInteger) ((ConditionVar) condition).x));
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
		Kit.control(Stream.of(list).anyMatch(x -> !x.dom.areInitValuesSubsetOf(values)));
		return forall(range(list.length), i -> {
			if (!list[i].dom.areInitValuesSubsetOf(values))
				api.extension(list[i], api.select(values, v -> list[i].dom.isPresentValue(v)));
		});
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, int[] occurs) {
		Kit.control(values.length == occurs.length);
		list = clean(list);
		if (mustBeClosed && Stream.of(list).anyMatch(x -> !((VariableInteger) x).dom.areInitValuesSubsetOf(values))) // 2nd part =
			// relevance of closed
			postClosed((VariableInteger[]) list, values);
		// should we return an object composed of the array above and the constraint below? Would it be useful ?
		return addCtr(new CardinalityConstant(this, (VariableInteger[]) list, values, occurs));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, int[] values, boolean mustBeClosed, Var[] occurs) {
		Kit.control(values.length == occurs.length && Stream.of(occurs).noneMatch(x -> x == null));
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
		Kit.control(values.length == occursMin.length && values.length == occursMax.length);
		list = clean(list);
		return addCtr(new CardinalityConstant(this, (VariableInteger[]) list, values, occursMin, occursMax));
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, int[] occurs) {
		Kit.control(values.length == occurs.length && Stream.of(values).noneMatch(x -> x == null));
		list = clean(list);
		return unimplemented("cardinality");
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, Var[] occurs) {
		Kit.control(values.length == occurs.length && Stream.of(values).noneMatch(x -> x == null) && Stream.of(occurs).noneMatch(x -> x == null));
		list = clean(list);
		return unimplemented("cardinality");
	}

	@Override
	public final CtrEntity cardinality(Var[] list, Var[] values, boolean mustBeClosed, int[] occursMin, int[] occursMax) {
		Kit.control(values.length == occursMin.length && values.length == occursMax.length && Stream.of(values).noneMatch(x -> x == null));
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
			if (rs.cp.settingGlobal.smartTable)
				return addCtr(minimum ? CtrExtensionSmart.buildMinimum(this, vars, y) : CtrExtensionSmart.buildMaximum(this, vars, y));
			return addCtr(minimum ? new Minimum(this, vars, y) : new Maximum(this, vars, y));
		}
		if (condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			Kit.control(op != EQ && op != NE);
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
		Kit.control(Stream.of(list).noneMatch(x -> x == null));
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
		Var[] tmp = replaceByVariables(trees);
		return minimum(tmp, condition);
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
		Var[] tmp = replaceByVariables(trees);
		return maximum(tmp, condition);
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
		if (rs.cp.settingGlobal.jokerTable)
			return extension(vars(index, list), Table.shortTuplesForElement(translate(list), (Variable) index, value), true);
		VariableInteger[] lst = Arrays.stream(list).map(v -> (VariableInteger) v).toArray(VariableInteger[]::new);
		return addCtr(new ElementConstant(this, lst, (VariableInteger) index, value));
	}

	@Override
	public final CtrAlone element(Var[] list, int startIndex, Var index, TypeRank rank, Var value) {
		unimplementedIf(startIndex != 0 || (rank != null && rank != TypeRank.ANY), "element");
		if (rs.cp.settingGlobal.smartTable)
			return addCtr(CtrExtensionSmart.buildElement(this, (VariableInteger[]) list, (VariableInteger) index, (VariableInteger) value));
		if (rs.cp.settingGlobal.jokerTable)
			return extension(Utilities.indexOf(value, list) == -1 ? vars(index, list, value) : vars(index, list),
					Table.shortTuplesForElement((Variable[]) list, (Variable) index, (Variable) value), true);
		VariableInteger[] lst = Arrays.stream(list).map(v -> (VariableInteger) v).toArray(VariableInteger[]::new);
		return addCtr(new ElementVariable(this, lst, (VariableInteger) index, (VariableInteger) value));
	}

	/**
	 * Builds a binary extension constraint because the vector is an array of integer values (and not variables).
	 */
	private final CtrEntity element(int[] list, int startIndex, Var index, Var value, int startValue) {
		List<int[]> l = new ArrayList<>();
		Domain x = ((VariableInteger) index).dom, z = ((VariableInteger) value).dom;
		for (int a = x.first(); a != -1; a = x.next(a)) {
			int v = x.toVal(a) - startIndex;
			if (0 <= v && v < list.length && z.isPresentValue(list[v] - startValue))
				l.add(new int[] { v + startIndex, list[v] - startValue });
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
		Utilities.control(Utilities.indexOf(index, list) == -1 && index != value, "index cannot be in vector or be the same variable as result");
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
							if (((Variable) value).dom.isPresentValue(w - startValue)) {
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
		Domain x = ((VariableInteger) rowIndex).dom, y = ((VariableInteger) colIndex).dom, z = ((VariableInteger) value).dom;
		for (int a = x.first(); a != -1; a = x.next(a))
			for (int b = y.first(); b != -1; b = y.next(b)) {
				int i = x.toVal(a), j = y.toVal(b);
				if (0 <= i && i < matrix.length && 0 <= j && j < matrix[i].length && z.isPresentValue(matrix[i][j]))
					l.add(new int[] { i, j, matrix[i][j] });
			}
		return api.extension(vars(rowIndex, colIndex, value), org.xcsp.common.structures.Table.clean(l));
	}

	@Override
	public CtrEntity element(Var[][] matrix, int startRowIndex, Var rowIndex, int startColIndex, Var colIndex, int value) {
		unimplementedIf(startRowIndex != 0 && startColIndex != 0, "element");
		if (rowIndex == colIndex) {
			Kit.control(matrix.length == matrix[0].length);
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
		Kit.control(Stream.of(list).noneMatch(x -> x == null));
		return unimplemented("channel");
	}

	@Override
	public CtrEntity channel(Var[] list1, int startIndex1, Var[] list2, int startIndex2) {
		Kit.control(Stream.of(list1).noneMatch(x -> x == null) && Stream.of(list2).noneMatch(x -> x == null));
		Kit.control(startIndex1 == 0 && startIndex2 == 0, () -> "unimplemented case for channel");
		// TODO : the two constraints above are not included in the object that is returned. Is that a problem?
		if (list1.length == list2.length) {
			allDifferent(list1);
			allDifferent(list2);
		}
		return forall(range(list1.length), i -> api.element(list2, list1[i], i));
	}

	@Override
	public final CtrEntity channel(Var[] list, int startIndex, Var value) {
		Kit.control(Stream.of(list).noneMatch(x -> x == null));
		Kit.control(Variable.areAllInitiallyBoolean((VariableInteger[]) list) && ((VariableInteger) value).dom.areInitValuesExactly(range(list.length)));
		return forall(range(list.length), i -> intension(iff(list[i], eq(value, i))));
	}

	// ************************************************************************
	// ***** Constraint stretch
	// ************************************************************************

	@Override
	public CtrEntity stretch(Var[] list, int[] values, int[] widthsMin, int[] widthsMax, int[][] patterns) {
		Kit.control(values.length == widthsMin.length && values.length == widthsMax.length);
		Kit.control(IntStream.range(0, values.length).allMatch(i -> widthsMin[i] <= widthsMax[i]));
		Kit.control(patterns == null || Stream.of(patterns).allMatch(t -> t.length == 2));
		return unimplemented("strtech");
	}

	// ************************************************************************
	// ***** Constraint noOverlap
	// ************************************************************************

	private CtrAlone noOverlap(Var x1, Var x2, int w1, int w2) {
		if (isBasicType(rs.cp.settingGlobal.typeNoOverlap))
			return addCtr(new Disjonctive(this, (Variable) x1, w1, (Variable) x2, w2));
		if (rs.cp.settingGlobal.typeNoOverlap == 2)
			return intension(or(le(add(x1, w1), x2), le(add(x2, w2), x1)));
		if (rs.cp.settingGlobal.typeNoOverlap == 10) // rs.cp.global.smartTable)
			return addCtr(CtrExtensionSmart.buildNoOverlap(this, (Variable) x1, (Variable) x2, w1, w2));
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
			int v = dom1.toVal(a);
			for (int b = dom2.last(); b != -1; b = dom2.prev(b)) {
				int w = dom2.toVal(b);
				if (v + offset > w)
					break;
				list.add(xAxis ? api.tuple(first ? v : w, first ? w : v, STAR, STAR) : api.tuple(STAR, STAR, first ? v : w, first ? w : v));
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

	private CtrAlone noOverlap(VariableInteger x1, VariableInteger x2, VariableInteger y1, VariableInteger y2, int w1, int w2, int h1, int h2) {
		if (rs.cp.settingGlobal.smartTable)
			return addCtr(CtrExtensionSmart.buildNoOverlap(this, x1, y1, x2, y2, w1, h1, w2, h2));
		if (rs.cp.settingGlobal.jokerTable)
			return extension(vars(x1, x2, y1, y2), computeTable(x1, x2, y1, y2, w1, w2, h1, h2), true, true);
		return intension(or(le(add(x1, w1), x2), le(add(x2, w2), x1), le(add(y1, h1), y2), le(add(y2, h2), y1)));
	}

	@Override
	public final CtrEntity noOverlap(Var[][] origins, int[][] lengths, boolean zeroIgnored) {
		// Kit.control(Kit.isRectangular(origins) && Kit.isRectangular(lengths) )
		unimplementedIf(!zeroIgnored, "noOverlap");
		return forall(range(origins.length).range(origins.length), (i, j) -> {
			if (i < j)
				noOverlap((VariableInteger) origins[i][0], (VariableInteger) origins[j][0], (VariableInteger) origins[i][1], (VariableInteger) origins[j][1],
						lengths[i][0], lengths[j][0], lengths[i][1], lengths[j][1]);
		});
	}

	private CtrAlone noOverlap(VariableInteger x1, VariableInteger x2, VariableInteger y1, VariableInteger y2, VariableInteger w1, VariableInteger w2,
			VariableInteger h1, VariableInteger h2) {
		if (rs.cp.settingGlobal.smartTable && Stream.of(w1, w2, h1, h2).allMatch(x -> x.dom.initSize() == 2))
			return addCtr(CtrExtensionSmart.buildNoOverlap(this, x1, y1, x2, y2, w1, h1, w2, h2));
		return intension(or(le(add(x1, w1), x2), le(add(x2, w2), x1), le(add(y1, h1), y2), le(add(y2, h2), y1)));
	}

	@Override
	public final CtrEntity noOverlap(Var[][] origins, Var[][] lengths, boolean zeroIgnored) {
		unimplementedIf(!zeroIgnored, "noOverlap");
		return forall(range(origins.length).range(origins.length), (i, j) -> {
			if (i < j)
				noOverlap((VariableInteger) origins[i][0], (VariableInteger) origins[j][0], (VariableInteger) origins[i][1], (VariableInteger) origins[j][1],
						(VariableInteger) lengths[i][0], (VariableInteger) lengths[j][0], (VariableInteger) lengths[i][1], (VariableInteger) lengths[j][1]);
		});
	}

	// ************************************************************************
	// ***** Constraint cumulative
	// ************************************************************************

	@Override
	public final CtrEntity cumulative(Var[] origins, int[] lengths, Var[] ends, int[] heights, Condition condition) {
		if (ends == null && condition instanceof ConditionVal) {
			TypeConditionOperatorRel op = ((ConditionVal) condition).operator;
			Kit.control(op == LT || op == LE);
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
		Utilities.control(Stream.of(list).noneMatch(x -> x == null), "A variable in array list is null");
		Utilities.control(list.length == phases.length, "Bad form of clause");
		Utilities.control(Variable.areAllInitiallyBoolean((VariableInteger[]) list), "A variable is not Boolean in the array list.");
		if (rs.cp.settingGlobal.typeClause == 1)
			return api.sum(list, Stream.of(phases).mapToInt(p -> p ? 1 : -1).toArray(), NE, -Stream.of(phases).filter(p -> !p).count());
		return unimplemented("clause");
	}

	// ************************************************************************
	// ***** Constraint instantiation
	// ************************************************************************

	@Override
	public final CtrEntity instantiation(Var[] list, int[] values) {
		Kit.control(list.length == values.length && list.length > 0);
		Kit.control(IntStream.range(0, list.length).noneMatch(i -> !((Variable) list[i]).dom.isPresentValue(values[i])), () -> "Pb");
		if (rs.cp.settingGlobal.typeInstantiation == 1)
			return forall(range(list.length), i -> equal(list[i], values[i]));
		return unimplemented("instantiation");
	}

	// ************************************************************************
	// ***** Meta-Constraint slide
	// ************************************************************************

	private int[] computeOffsets(IVar[][] lists, IVar[] scp0, IVar[] scp1) {
		return IntStream.range(0, lists.length).map(i -> {
			int pos0 = Stream.of(scp0).filter(x -> Utilities.indexOf(x, lists[i]) >= 0).mapToInt(x -> Utilities.indexOf(x, lists[i])).min().orElse(-1);
			int pos1 = Stream.of(scp1).filter(x -> Utilities.indexOf(x, lists[i]) >= 0).mapToInt(x -> Utilities.indexOf(x, lists[i])).min().orElse(-1);
			Kit.control(pos0 != -1 && pos1 != -1);
			return pos1 - pos0;
		}).toArray();
	}

	private int[] computeCollects(IVar[][] lists, IVar[] scp) {
		return IntStream.range(0, lists.length).map(i -> (int) Stream.of(scp).filter(x -> Utilities.indexOf(x, lists[i]) >= 0).count()).toArray();
	}

	@Override
	public final CtrEntity slide(IVar[] list, Range range, IntFunction<CtrEntity> template) {
		Kit.control(range.start == 0 && range.length() > 0);
		if (range.length() == 1)
			return template.apply(0);
		return manageLoop(() -> IntStream.range(0, range.stop).filter(i -> i % range.step == 0).mapToObj(i -> (CtrHard) ((CtrAlone) template.apply(i)).ctr)
				.toArray(CtrHard[]::new));
	}

	// public final CtrEntity slide(IVar[] list1, IVar[] list2, Range range, IntFunction<CtrAlone> template, TypeClass... classes) {
	// if (rs.cp.export != EExport.NO)
	// return addCtr(new Slide(this, list1, list2, range, template), classes);
	// return manageLoop(() -> Slide.buildCtrsFor(range, template), classes);
	// }

	// public final CtrEntity slide(IVar[][] lists, int[] offsets, int[] collects, CtrHard[] ctrs, TypeClass... classes) {
	// if (rs.cp.export != EExport.NO)
	// return addCtr(new Slide(this, lists, offsets, collects, ctrs), classes);
	// return ctrEntities.newCtrArrayEntity(ctrs, false, classes);
	// }

	// ************************************************************************
	// ***** Meta-Constraint ifThen
	// ************************************************************************

	@Override
	public final CtrEntity ifThen(CtrEntity c1, CtrEntity c2) {
		Utilities.control(c1 instanceof CtrAlone && c2 instanceof CtrAlone, "unimplemented for the moment");
		return (CtrEntity) Kit.exit("unimplemented case for ifThen");
	}

	// ************************************************************************
	// ***** Meta-Constraint ifThenElse
	// ************************************************************************

	@Override
	public final CtrEntity ifThenElse(CtrEntity c1, CtrEntity c2, CtrEntity c3) {
		Utilities.control(c1 instanceof CtrAlone && c2 instanceof CtrAlone && c3 instanceof CtrAlone, "unimplemented for the moment");
		return (CtrEntity) Kit.exit("unimplemented case for ifThenElse");
	}

	// ************************************************************************
	// ***** Constraint smart
	// ************************************************************************

	/** Builds and returns a smart constraint. */
	public final CtrAlone smart(IVar[] scp, SmartTuple... smartTuples) {
		return addCtr(new CtrExtensionSmart(this, translate(scp), smartTuples));
	}

	/**
	 * Builds a constraint that holds when at least k variables of the scope take the corresponding value in the specified tuple.
	 */
	public CtrEntity tupleProximityGE(IVar[] scope, int[] tuple, int k, boolean noModidictaion) {
		Kit.control(scope.length != 0);
		if (noModidictaion)
			return addCtr(new HammingProximityConstantGE(this, (Variable[]) scope, tuple, k));
		List<IVar> newScope = new ArrayList<>();
		List<Integer> newTuple = new ArrayList<>();
		int newK = k;
		for (int i = 0; i < scope.length; i++)
			if (((Variable) scope[i]).dom.isPresentValue(tuple[i]))
				if (((Variable) scope[i]).dom.size() > 1) {
					newScope.add(scope[i]);
					newTuple.add(tuple[i]);
				} else
					newK--;
		if (newK <= 0)
			return ctrEntities.new CtrAloneDummy("Removed constraint due to newk <= 0");
		if (newK == newScope.size())
			return forall(range(scope.length), i -> equal(scope[i], tuple[i]));
		Kit.control(newK < newScope.size(), () -> "Instance is UNSAT, constraint with scope " + Kit.join(scope) + " cannot have more than " + k
				+ " variables equal to their corresponding value in " + Kit.join(tuple));
		return addCtr(new HammingProximityConstantGE(this, newScope.toArray(new Variable[newScope.size()]), Kit.intArray(newTuple), newK));
	}

	public CtrEntity tupleProximityDistanceSum(IVar[] scope, int[] tuple, int maxDist) {
		return addCtr(new HammingProximityConstantSumLE(this, translate(scope), tuple, maxDist));
	}

	// ************************************************************************
	// ***** Managing objectives
	// ************************************************************************

	public final static String vfsComment = "Either you set -f=cop or you set -f=csp together with -vfs=v where v is an integer value forcing the value of the objective.";

	private OptimizationPilot buildOptimizationPilot(TypeOptimization opt, CtrAlone c) {
		control(optimizationPilot == null, "Only mono-objective currently supported");
		control(c.ctr instanceof OptimizationCompatible);
		framework = TypeFramework.COP;
		rs.cp.toCOP();
		String suffix = Kit.camelCaseOf(rs.cp.settingOptimization.optimizationStrategy.name());
		if (suffix.equals("Decreasing"))
			return new OptimizationPilotDecreasing(this, opt, (OptimizationCompatible) c.ctr);
		if (suffix.equals("Increasing"))
			return new OptimizationPilotIncreasing(this, opt, (OptimizationCompatible) c.ctr);
		control(suffix.equals("Dichotomic"));
		return new OptimizationPilotDichotomic(this, opt, (OptimizationCompatible) c.ctr);

		// the code below does not work (certainly because the target class is intern)
		// return Reflector.buildObject("OptimizationPilotDecreasing", OptimizationPilot.class, this, opt, c.ctr);
	}

	private boolean switchToSatisfaction(TypeOptimization opt, TypeObjective obj, int[] coeffs, IVar... list) {
		long limit = rs.cp.settingGeneral.limitForSatisfaction;
		if (limit == PLUS_INFINITY)
			return false;
		framework = TypeFramework.CSP;
		rs.cp.settingGeneral.framework = TypeFramework.CSP;
		rs.cp.settingGeneral.nSearchedSolutions = 1;
		if (obj == EXPRESSION) {
			control(list.length == 1 && coeffs == null);
			intension(opt == MINIMIZE ? XNodeParent.le(list[0], limit) : XNodeParent.ge(list[0], limit));
		}
		if (coeffs != null) {
			control(obj == SUM);
			sum(list, coeffs, opt == MINIMIZE ? LE : GE, limit);
		} else {
			control(obj.generalizable());
			if (opt == MINIMIZE) {
				if (obj == SUM)
					addCtr(new SumSimpleLE(this, translate(list), limit));
				else if (obj == MINIMUM)
					addCtr(new MinimumCstLE(this, translate(list), limit));
				else if (obj == MAXIMUM)
					forall(range(list.length), i -> lessEqual(list[i], limit));
				else
					addCtr(new NValuesLE(this, translate(list), (int) limit));
			} else {
				if (obj == SUM)
					addCtr(new SumSimpleGE(this, translate(list), limit));
				else if (obj == MINIMUM)
					forall(range(list.length), i -> greaterEqual(list[i], limit));
				else if (obj == MAXIMUM)
					addCtr(new MaximumCstGE(this, translate(list), limit));
				else
					addCtr(new NValuesGE(this, translate(list), (int) limit));
			}
		}
		return true;
	}

	@Override
	public final ObjEntity minimize(IVar x) {
		if (!switchToSatisfaction(MINIMIZE, EXPRESSION, null, x)) {
			CtrAlone c = addCtr(new ObjVarLE(this, (VariableInteger) x, Math.min(rs.cp.settingOptimization.upperBound, Integer.MAX_VALUE)));
			optimizationPilot = buildOptimizationPilot(MINIMIZE, c);
		}
		return null;
	}

	@Override
	public final ObjEntity maximize(IVar x) {
		if (!switchToSatisfaction(MAXIMIZE, EXPRESSION, null, x)) {
			CtrAlone c = addCtr(new ObjVarGE(this, (VariableInteger) x, Math.max(rs.cp.settingOptimization.lowerBound, Integer.MIN_VALUE)));
			optimizationPilot = buildOptimizationPilot(MAXIMIZE, c);
		}
		return null;

	}

	@Override
	public final ObjEntity minimize(XNode<IVar> tree) {
		return minimize(replaceByVariable(tree));
	}

	@Override
	public final ObjEntity maximize(XNode<IVar> tree) {
		return maximize(replaceByVariable(tree));
	}

	@Override
	public final ObjEntity minimize(TypeObjective type, IVar[] list) {
		control(type.generalizable());
		if (!switchToSatisfaction(MINIMIZE, type, null, list)) {
			int limit = (int) Math.min(rs.cp.settingOptimization.upperBound, type == NVALUES ? list.length : Integer.MAX_VALUE);
			CtrAlone c = null;
			if (type == SUM)
				c = addCtr(new SumSimpleLE(this, translate(list), limit));
			else if (type == MINIMUM)
				c = addCtr(new MinimumCstLE(this, translate(list), limit));
			else if (type == MAXIMUM)
				c = addCtr(new MaximumCstLE(this, translate(list), limit));
			else
				c = addCtr(new NValuesLE(this, translate(list), limit));
			optimizationPilot = buildOptimizationPilot(MINIMIZE, c);
		}
		return null;
	}

	@Override
	public final ObjEntity maximize(TypeObjective type, IVar[] list) {
		control(type.generalizable());
		if (!switchToSatisfaction(MAXIMIZE, type, null, list)) {
			int limit = (int) Math.max(rs.cp.settingOptimization.lowerBound, type == NVALUES ? 1 : Integer.MIN_VALUE);
			CtrAlone c = null;
			if (type == SUM)
				c = addCtr(new SumSimpleGE(this, translate(list), limit));
			else if (type == MINIMUM)
				c = addCtr(new MinimumCstGE(this, translate(list), limit));
			else if (type == MAXIMUM)
				c = addCtr(new MaximumCstGE(this, translate(list), limit));
			else
				c = addCtr(new NValuesGE(this, translate(list), limit));
			optimizationPilot = buildOptimizationPilot(MAXIMIZE, c);
		}
		return null;
	}

	@Override
	public final ObjEntity minimize(TypeObjective type, IVar[] list, int[] coeffs) {
		control(type == SUM && coeffs != null);
		if (!switchToSatisfaction(MINIMIZE, type, coeffs, list))
			optimizationPilot = buildOptimizationPilot(MINIMIZE, sum(list, coeffs, LE, rs.cp.settingOptimization.upperBound, false));
		return null;
	}

	@Override
	public final ObjEntity maximize(TypeObjective type, IVar[] list, int[] coeffs) {
		control(type == SUM && coeffs != null);
		if (!switchToSatisfaction(MAXIMIZE, type, coeffs, list))
			optimizationPilot = buildOptimizationPilot(MAXIMIZE, sum(list, coeffs, GE, rs.cp.settingOptimization.lowerBound, false));
		return null;
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
		if (rs.cp.settingGeneral.enableAnnotations)
			super.decisionVariables(list);
	}

}
