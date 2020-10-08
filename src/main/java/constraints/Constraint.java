/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints;

import static org.xcsp.common.Constants.ALL;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.modeler.definitions.ICtr;

import constraints.hard.ConflictsStructure;
import constraints.hard.CtrExtension;
import constraints.hard.extension.structures.ExtensionStructure;
import heuristics.variables.dynamic.HeuristicVariablesConflictBased;
import interfaces.FilteringGlobal;
import interfaces.FilteringSpecific;
import interfaces.ObserverConstruction;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagGACUnguaranteed;
import interfaces.TagSymmetric;
import interfaces.TagUnsymmetric;
import problem.Problem;
import propagation.structures.supporters.Supporter;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import utility.exceptions.MissingImplementationException;
import utility.exceptions.UnreachableCodeException;
import utility.operations.Calculator;
import utility.sets.SetDense;
import utility.sets.SetSparse;
import variables.Variable;
import variables.domains.Domain;
import variables.domains.DomainHuge;

/**
 * This class gives the description of a constraint. <br>
 * A constraint is attached to a problem and is uniquely identified by a number called <code>id</code>.<br>
 * A constraint involves a subset of variables of the problem.
 */
public abstract class Constraint implements ICtr, ObserverConstruction, Comparable<Constraint> {

	@Override
	public int compareTo(Constraint c) {
		boolean b1 = id == null, b2 = c.id == null; // b1 and b2 true iff canonical ids
		return b1 && !b2 ? -1 : !b1 && b2 ? 1 : !b1 && !b2 ? id.compareTo(c.id) : Integer.compare(num, c.num);

	}

	@Override
	public void onConstructionProblemFinished() {
		// sets the position of all the variables of the problem with respect to the set of variables of the constraint.
		// If a variable does not belong to the constraint, then its position is set to -1
		if (pb.rs.cp.settingCtrs.arityLimitForVapArray < scp.length
				&& (pb.variables.length < pb.rs.cp.settingCtrs.arityLimitForVapArrayUB || scp.length > pb.variables.length / 3)) {
			this.vaps = Kit.repeat(-1, pb.variables.length);
			for (int i = 0; i < scp.length; i++)
				this.vaps[scp[i].num] = i;

		} else
			this.vaps = null;
		// this.variableManager = new VariableManagerConstraint(vaps == null, scp.length);
		control(true);
	}

	/*************************************************************************
	 ***** Static
	 *************************************************************************/

	public static final int MAX_FILTERING_COMPLEXITY = 2;

	private static Map<String, int[]> symmetryMatchings = Collections.synchronizedMap(new HashMap<String, int[]>());

	public static int[] getSymmetryMatching(String key) {
		synchronized (symmetryMatchings) {
			return symmetryMatchings.get(key);
		}
	}

	public static void putSymmetryMatching(String key, int[] value) {
		synchronized (symmetryMatchings) {
			symmetryMatchings.put(key, value);
		}
	}

	/**
	 * A special constraint that can be used (for instance) by methods that requires returning three-state values (null,a problem constraint, this
	 * special marker).
	 */
	public static final Constraint TAG = new CtrHard() {
		@Override
		public boolean checkValues(int[] t) {
			throw new UnreachableCodeException();
		}
	};

	public static int nPairsOfCtrsWithSimilarScopeIn(Constraint... ctrs) {
		return IntStream.range(0, ctrs.length)
				.map(i -> (int) IntStream.range(i + 1, ctrs.length).filter(j -> Variable.areSimilarArrays(ctrs[i].scp, ctrs[j].scp)).count()).sum();
	}

	public static final boolean areNumsNormalized(Constraint[] ctrs) {
		return IntStream.range(0, ctrs.length).noneMatch(i -> i != ctrs[i].num);
	}

	public static final boolean isInvolvingAbsentVar(Constraint c, boolean[] presentVars) {
		return Stream.of(c.scp).anyMatch(x -> !presentVars[x.num]);
	}

	public static final boolean isGuaranteedGACOn(Constraint[] ctrs) {
		return Stream.of(ctrs).allMatch(c -> c.isGuaranteedGAC());
	}

	public static final long costOfCoveredConstraintsIn(Constraint[] ctrs) {
		// return Stream.of(ctrs).filter(c -> c.futvars.size() == 0).mapToLong(c -> c.costOfCurrInstantiation())
		// .reduce(0, (s, t) -> Calculator.add(s, t)); !!!! too costly
		// try with java ac problems.tran.Wcsp ~/instances2/wcsp/5.wcsp -f=wcsp -ev -p=BTSoft -ct=delta -valh=First -rc=10 -rn=100
		long cost = 0;
		for (Constraint c : ctrs)
			if (c.futvars.size() == 0)
				cost = Calculator.add(cost, c.costOfCurrInstantiation());
		return cost;
	}

	public static final int howManyVarsWithin(int[] sizes, int spaceLimitation) {
		double limit = Math.pow(2, spaceLimitation);
		Arrays.sort(sizes);
		double prod = 1;
		int i = sizes.length - 1;
		for (; i >= 0 && prod <= limit; i--)
			prod = prod * sizes[i];
		return prod > limit ? (sizes.length - i - 1) : ALL;
	}

	public static final int howManyVarsWithin(Variable[] vars, int spaceLimitation) {
		return howManyVarsWithin(Stream.of(vars).mapToInt(x -> x.dom.size()).toArray(), spaceLimitation);
	}

	/*************************************************************************
	 * Fields
	 *************************************************************************/

	/** The problem to which the constraint belongs. */
	public final Problem pb;

	/** The number of the constraint; it is <code>-1</code> when not fully initialized or not a direct constraint of the problem. */
	public int num = -1;

	/** The id (name) of the constraint. */
	private String id;

	/** The scope of the constraint, i.e. the set of variables involved in the constraint. */
	public final Variable[] scp;

	/**
	 * The position of all variables of the problem in the constraint. vaps[vid] gives the position of the variable with id vid in the scope of the
	 * constraint, or -1 if it is not involved. For example, <code> vaps[i] = j </code> iff the variable x such that <code> x.id = i </code> is the
	 * jth variable involved in the constraint. For constraint of small arity, not necessarily built. So, you need to call <code> getVapOf </code>
	 * instead of acessing directly this field.
	 */
	private int[] vaps;

	public SetDense futvars;

	/** Indicates if the constraint must be ignored. */
	public boolean ignored;

	/** The key of the constraint. Used for symmetry detection. */
	public String key;

	/** The assistant which manages the tuples of the constraint. */
	public final TupleManager tupleManager;

	protected Supporter<? extends Constraint> supporter;

	/**
	 * The weighted degree of this constraint. <br />
	 * Its value is equal to 1 + the number of times this constraint has been involved in a revision generating a domain wipeout. <br />
	 * It used by conflict-directed variable ordering heuristics [Boussemart, Hemery, Lecoutre, Sais 2004].
	 */
	// private double wdeg;

	/**
	 * The weighted degrees attached to the variables involved in the scope. wdegs[x] gives the weighted degree of the variable (at position) x in the
	 * scope.
	 */
	// public double[] wdegs;

	/** Indicates if for each domain of a variable involved in the constraint, the index of any value corresponds to this value. */
	public final boolean indexesMatchValues;

	/** This field is used to store a tuple of (int) values. Is is inserted as a field in order to avoid overhead of memory allocations. */
	protected final int[] vals;

	public final Domain[] doms;

	public int cost = 1;

	public long timestamp;

	public int filteringComplexity;

	/**
	 * Indicates if filtering (e.g. GAC) must be controlled. If the number of uninstantiated variables is greater than this value, filtering is not
	 * achieved.
	 */
	public final int genericFilteringThreshold;

	public int nEffectiveFilterings;

	public Variable[] hugeDomainVars;

	public Object data;

	/**********************************************************************************************
	 * Accessors
	 *********************************************************************************************/

	public final String defaultId() {
		return "c" + num;
	}

	public final String explicitId() {
		return id;
	}

	public final String getId() {
		return id != null ? id : defaultId();
	}

	public final Constraint setId(String id) {
		this.id = id;
		return this;
	}

	public Boolean isSymmetric() {
		if (this instanceof TagSymmetric)
			return Boolean.TRUE;
		if (this instanceof TagUnsymmetric)
			return Boolean.FALSE;
		return null;
	}

	public int[] defineSymmetryMatching() {
		Boolean b = isSymmetric();
		Kit.control(b != null);
		return b ? Kit.repeat(1, scp.length) : Kit.range(1, scp.length);
	}

	public final int[] getSymmetryMatching() {
		return getSymmetryMatching(key);
	}

	public void handleEffectiveFilterings() {
		if (pb.solver instanceof SolverBacktrack)
			((SolverBacktrack) pb.solver).proofer.updateProof(this);// TODO // ((SystematicSolver)solver).updateProofAll();
		nEffectiveFilterings++;
		pb.stuff.nEffectiveFilterings++;
	}

	public final int computeGenericFilteringThreshold() {
		if (this instanceof FilteringSpecific || this instanceof CtrExtension)
			return Integer.MAX_VALUE; // because not concerned
		int arityLimit = pb.rs.cp.settingPropagation.arityLimitForGACGuaranteed;
		if (scp.length <= arityLimit)
			return Integer.MAX_VALUE;
		int futureLimitation = pb.rs.cp.settingPropagation.futureLimitation;
		if (futureLimitation != -1)
			return futureLimitation < scp.length ? Math.max(arityLimit, futureLimitation) : Integer.MAX_VALUE;
		int spaceLimitation = pb.rs.cp.settingPropagation.spaceLimitation;
		if (spaceLimitation != -1)
			return Math.max(arityLimit, howManyVarsWithin(scp, spaceLimitation));
		return Integer.MAX_VALUE;
	}

	public boolean completeFilteringAtEachCall() {
		if (this instanceof TagFilteringCompleteAtEachCall)
			return true;
		if (this instanceof TagFilteringPartialAtEachCall)
			return false;
		throw new MissingImplementationException(getClass().getName()); // to force the user to tag constraints or override the function
	}

	public boolean isGuaranteedGAC() {
		if (this.hugeDomainVars.length > 0)
			return false;
		if (this instanceof TagGACGuaranteed)
			return true;
		if (this instanceof TagGACUnguaranteed)
			return false;
		if (this instanceof FilteringSpecific)
			throw new MissingImplementationException(getClass().getName()); // to force the user to tag constraints or override the function
		else
			return genericFilteringThreshold == Integer.MAX_VALUE;
	}

	// public final boolean canBeCurrentlyGenericallyFiltered() {
	// return futvars.size() > 0 && futvars.size() <= genericFilteringThreshold;
	// }

	/**
	 * @return the position of the variable or <code>-1</code> if the variable is not involved in the constraint
	 */
	public final int positionOf(Variable x) {
		if (vaps != null)
			return vaps[x.num];
		for (int i = scp.length - 1; i >= 0; i--)
			if (scp[i] == x)
				return i;
		return -1;
	}

	/** Determines if the specified variable is involved in this constraint. */
	public final boolean involves(Variable x) {
		return positionOf(x) != -1;
	}

	/** Determines if the specified variables are involved in this constraint. */
	public final boolean involves(Variable x, Variable y) {
		return positionOf(x) != -1 && positionOf(y) != -1;
	}

	public final boolean isScopeCoveredBy(Variable[] vars) {
		for (int cnt = 0, i = 0; i < vars.length; i++)
			if (involves(vars[i]))
				if (++cnt == scp.length)
					return true;
		return false;
	}

	public Supporter<? extends Constraint> supporter() {
		return supporter;
	}

	public abstract void buildSupporter();

	/**
	 * Returns the weighted degree of the constraint.
	 */
	public final double wdeg() {
		return ((HeuristicVariablesConflictBased) ((SolverBacktrack) pb.solver).heuristicVars).cscores[num];
	}

	// public final void resetWdeg() { // called by wdeg-based heuristics, possibly before each new run
	// this.wdeg = 0; // pb.rs.cp.varh.initialWdeg;
	// this.wdegs = this.wdegs == null ? new double[scp.length] : this.wdegs;
	// // double d = 1.0 / scp.length;
	// Arrays.fill(this.wdegs, 0); // 1/(double)pb.rs.cp.varh.weighting == EWeighting.CACD ? 0 : pb.rs.cp.varh.initialWdeg);
	// }

	// public final void updateNegativelyWdegOf(int x) {
	// scp[x].wdeg += -wdegs[x];
	// }
	//
	// public final void updatePositivelyWdegOf(int x) {
	// scp[x].wdeg += wdegs[x];
	// }
	//
	// int cnt = 0;
	//
	// public final void incrementWdegBy(double increment) {
	// // System.out.println("inc " + this);
	// for (int i = futvars.limit; i >= 0; i--) {
	// int x = futvars.dense[i];
	// if (pb.rs.cp.varh.weighting == EWeighting.CACD) { // in this case, the increment is not 1 as for UNIT
	// Domain dom = scp[x].dom;
	// boolean test = false; // hard coding ; does not seem to be interesting, as variant
	// if (test) {
	// int depth = pb.solver.depth();
	// int nRemoved = 0;
	// for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
	// if (dom.getRemovedLevelOf(a) != depth)
	// break;
	// nRemoved++;
	// }
	// increment = 1.0 / (futvars.size() * (dom.size() + nRemoved));
	// } else
	// increment = 1.0 / (futvars.size() * (dom.size() == 0 ? 0.5 : dom.size()));
	// }
	// // System.out.println("increm " + increment + " " + scp[x] + " " + scp[x].num);
	// wdeg += increment;
	// scp[x].wdeg += increment;
	// // double d = IntStream.range(0, scp.length).mapToDouble(j -> scp[j].wdeg).sum();
	// // assert wdeg == d : wdeg + " " + d;
	// wdegs[x] += increment;
	//
	// }
	//
	// // if (cnt++ % 100 == 0) {
	// // System.out.println("fff " + pb.rs.cp.varh.weighting + " " + increment);
	// // for (Variable x : pb.variables)
	// // System.out.print(x.wdeg + " ");
	// // System.out.println();
	// // }
	// }

	public ExtensionStructure extStructure() {
		return null;
	}

	public ConflictsStructure conflictsStructure() {
		return null;
	}

	public void cloneStructures(boolean onlyConflictsStructure) {}

	public final void reset() {
		Kit.control(futvars.free() == 0);
		// if (!preserveWeightedDegrees)
		// resetWdeg();
		nEffectiveFilterings = 0;
		timestamp = 0;
	}

	/**********************************************************************************************
	 * Constructors
	 *********************************************************************************************/

	/**
	 * Private constructor just used to build the TAG constraint.
	 */
	protected Constraint() {
		this.pb = null;
		this.scp = new Variable[0];
		this.tupleManager = null;
		this.vals = null;
		this.doms = null;
		this.genericFilteringThreshold = Integer.MAX_VALUE;
		this.indexesMatchValues = false;
		this.hugeDomainVars = new Variable[0];
	}

	public Constraint(Problem pb, Variable[] scp) {
		this.pb = pb;
		scp = Stream.of(scp).distinct().toArray(Variable[]::new);
		this.scp = scp;
		assert scp.length >= 1 && Stream.of(scp).allMatch(x -> x != null) && Variable.areAllDistinct(scp) : this + " with a scope badly formed ";
		Stream.of(scp).forEach(x -> x.collectedCtrs.add(this));
		this.hugeDomainVars = Stream.of(scp).filter(x -> x.dom instanceof DomainHuge).toArray(Variable[]::new);

		this.doms = Variable.buildDomainsArrayFor(scp);
		this.tupleManager = new TupleManager(this.doms.clone());
		this.vals = new int[scp.length];

		this.genericFilteringThreshold = computeGenericFilteringThreshold();
		this.indexesMatchValues = Stream.of(scp).allMatch(x -> x.dom.indexesMatchValues());

		if (this instanceof FilteringSpecific)
			pb.stuff.nSpecificCtrs++;
		if (this instanceof FilteringGlobal)
			pb.stuff.nGlobalCtrs++;
		if (this instanceof ObserverConstruction)
			pb.rs.observersConstruction.add(this);
		// below scp.length <= pb.rs.cp.arityLimitForVapArray means vap==null
		this.futvars = scp.length <= pb.rs.cp.settingCtrs.arityLimitForVapArray ? new SetDense(scp.length, true) : new SetSparse(scp.length, true);

	}

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	public final void doPastVariable(Variable x) {
		if (vaps != null && futvars instanceof SetSparse)
			((SetSparse) futvars).remove(vaps[x.num]);
		else
			for (int i = futvars.limit; i >= 0; i--) {
				if (scp[futvars.dense[i]] == x) {
					futvars.removeAtPosition(i);
					break;
				}
			}
		// if (wdegs != null && futvars.size() == 1) // TODO rather using observers?
		// updateNegativelyWdegOf(futvars.dense[0]);
	}

	public final void undoPastVariable(Variable x) {
		assert x.isAssigned() && scp[futvars.dense[futvars.size()]] == x;
		// if (wdegs != null && futvars.size() == 1) // TODO rather using observers?
		// updatePositivelyWdegOf(futvars.dense[0]);
		futvars.limit++;
	}

	public int[] buildCurrentInstantiationTuple() {
		int[] tuple = tupleManager.localTuple;
		for (int i = tuple.length - 1; i >= 0; i--)
			tuple[i] = doms[i].unique();
		return tuple;
	}

	/**
	 * Transforms all indexes of the given tuple into values. Elements of the tuple must then correspond to index of values occurring in the domains
	 * of the variables involved in the constraint.
	 */
	public int[] toVals(int[] idxs) {
		for (int i = vals.length - 1; i >= 0; i--)
			vals[i] = doms[i].toVal(idxs[i]);
		return vals;
	}

	public int[] toIdxs(int[] vals, int[] idxs) {
		for (int i = vals.length - 1; i >= 0; i--)
			idxs[i] = doms[i].toIdx(vals[i]);
		return idxs;
	}

	/**
	 * Determines if the given tuple (usually a support) is still valid. We have just to test that all indexes are still in the domains of the
	 * variables involved in the constraint. Do not call the <code> check </code> method instead since it can not take into account removed values.
	 * 
	 * @param tuple
	 *            a given tuple of indexes (of values)
	 * @return <code> true </code> iff the tuple is valid
	 */
	public final boolean isValid(int[] tuple) {
		for (int i = tuple.length - 1; i >= 0; i--)
			if (!doms[i].isPresent(tuple[i]))
				return false;
		return true;
	}

	public long costOfCurrInstantiation() {
		return costOfIdxs(buildCurrentInstantiationTuple());
	}

	public abstract long costOfIdxs(int[] idxs);

	public abstract long minCostOfTuplesWith(int vap, int idx);

	public abstract boolean filterFrom(Variable evt);

	/**
	 * We assume that the given array corresponds to a tuple of indexes (and not to a tuple of values).
	 * 
	 * @param idxs
	 *            the tuple to be removed
	 */
	public boolean removeTuple(int... idxs) {
		throw new UnreachableCodeException();
	}

	public abstract boolean isSubstitutableBy(Variable var, int idx1, int idx2);

	public abstract boolean controlArcConsistency();

	public void control(boolean conditionToBeRespected) {
		Kit.control(conditionToBeRespected);
	}

	public StringBuilder signature() {
		return Variable.signatureFor(scp);
	}

	@Override
	public String toString() {
		return getId() + "(" + Variable.joinNames(scp, ",") + ")";
	}

	public void display(boolean exhaustively) {
		Kit.log.finer("Constraint " + toString());
		Kit.log.finer("\tClass = " + getClass().getName()
				+ (this instanceof CtrExtension ? ":" + ((CtrExtension) this).extStructure().getClass().getSimpleName() : ""));
		Kit.log.finer("\tKey = " + key);
		int[] t = getSymmetryMatching(key);
		Kit.log.finer("\tSymmetryMatching = " + (t == null ? " undefined " : Kit.join(t)));
		Kit.log.finer("\tCost = " + cost);
		// Kit.log.finer("\tXCSP = " + defXCSP());
	}

	protected String compact(Variable[] vars) {
		return pb.varEntities.compact(vars);
	}

	protected String compactOrdered(Variable[] vars) {
		return pb.varEntities.compactOrdered(vars);
	}

}
