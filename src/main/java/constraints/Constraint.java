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

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.definitions.ICtr;

import constraints.extension.Extension;
import constraints.extension.structures.Bits;
import constraints.extension.structures.ExtensionStructure;
import constraints.global.SumSimple.SumSimpleEQ;
import constraints.global.SumWeighted.SumWeightedEQ;
import constraints.intension.Intension;
import dashboard.ControlPanel.SettingCtrs;
import executables.Resolution;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
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
import propagation.Forward;
import propagation.Reviser;
import propagation.Supporter;
import propagation.Supporter.SupporterHard;
import search.backtrack.SolverBacktrack;
import sets.SetDense;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.DomainInfinite;
import variables.Variable;

/**
 * This class gives the description of a constraint. <br>
 * A constraint is attached to a problem and is uniquely identified by a number <code>num</code> and an identifier <code>id</code>.<br>
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
		// If a variable does not belong to the constraint, then its position is set to -1
		if (settings.arityLimitForVapArrayLb < scp.length && (pb.variables.length < settings.arityLimitForVapArrayUb || scp.length > pb.variables.length / 3)) {
			this.positions = Kit.repeat(-1, pb.variables.length);
			for (int i = 0; i < scp.length; i++)
				this.positions[scp[i].num] = i;
			this.futvars = new SetSparse(scp.length, true);
		} else {
			this.positions = null;
			this.futvars = new SetDense(scp.length, true);
		}
		control(true);
	}

	/*************************************************************************
	 ***** Two very special kinds of constraints and CtrGlobal
	 *************************************************************************/

	public static class CtrHardFalse extends Constraint implements FilteringSpecific, TagFilteringCompleteAtEachCall, TagGACGuaranteed {

		@Override
		public boolean checkValues(int[] t) {
			return false;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			return false;
		}

		public String message;

		public CtrHardFalse(Problem pb, Variable[] scp, String message) {
			super(pb, scp);
			this.message = message;
		}
	}

	public static class CtrHardTrue extends Constraint implements FilteringSpecific, TagFilteringCompleteAtEachCall, TagGACGuaranteed {

		@Override
		public boolean checkValues(int[] t) {
			return true;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			return true;
		}

		public CtrHardTrue(Problem pb, Variable[] scp) {
			super(pb, scp);
		}
	}

	public static abstract class CtrGlobal extends Constraint implements FilteringGlobal {

		protected final void defineKey(Object... specificData) {
			StringBuilder sb = signature().append(' ').append(getClass().getSimpleName());
			for (Object data : specificData)
				sb.append(' ').append(data.toString());
			this.key = sb.toString(); // getSignature().append(' ').append(this.getClass().getSimpleName()).append(' ') + o.toString();
		}

		public CtrGlobal(Problem pb, Variable[] scp) {
			super(pb, scp);
			filteringComplexity = 1;
		}
	}

	/*************************************************************************
	 ***** Static
	 *************************************************************************/

	public static final int MAX_FILTERING_COMPLEXITY = 2;

	/**
	 * A special constraint that can be used (for instance) by methods that requires returning three-state values (null,a problem constraint, this special
	 * marker).
	 */
	public static final Constraint TAG = new Constraint() {
		@Override
		public boolean checkValues(int[] t) {
			throw new AssertionError();
		}
	};

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

	public static final boolean isGuaranteedGAC(Constraint[] ctrs) {
		return Stream.of(ctrs).allMatch(c -> c.isGuaranteedAC());
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

	public static Constraint firstUnsatisfiedHardConstraint(Constraint[] constraints, int[] solution) {
		for (Constraint c : constraints) {
			if (c.ignored)
				continue;
			int[] tmp = c.tupleManager.localTuple;
			for (int i = 0; i < tmp.length; i++)
				tmp[i] = solution != null ? solution[c.scp[i].num] : c.scp[i].dom.unique();
			if (c.checkIndexes(tmp) == false)
				return c;
		}
		return null;
	}

	public static Constraint firstUnsatisfiedHardConstraint(Constraint[] constraints) {
		return firstUnsatisfiedHardConstraint(constraints, null);
	}

	public static int nPairsOfCtrsWithSimilarScopeIn(Constraint... ctrs) {
		return IntStream.range(0, ctrs.length)
				.map(i -> (int) IntStream.range(i + 1, ctrs.length).filter(j -> Variable.areSimilarArrays(ctrs[i].scp, ctrs[j].scp)).count()).sum();
	}

	public static final boolean areNumsNormalized(Constraint[] ctrs) {
		return IntStream.range(0, ctrs.length).noneMatch(i -> i != ctrs[i].num);
	}

	public static final boolean isPresentScope(Constraint c, boolean[] presentVars) {
		return Stream.of(c.scp).allMatch(x -> presentVars[x.num]);
	}

	public static final long costOfCoveredConstraintsIn(Constraint[] ctrs) {
		// using streams is too costly
		long cost = 0;
		for (Constraint c : ctrs)
			if (c.futvars.size() == 0)
				cost = Kit.addSafe(cost, c.costOfCurrInstantiation());
		return cost;
	}

	/*************************************************************************
	 * Fields
	 *************************************************************************/

	/** The problem to which the constraint belongs. */
	public final Problem pb;

	/** The number of the constraint; it is <code>-1</code> when not fully initialized or not a direct constraint of the problem. */
	public int num = -1;

	/** The id (identifier or name) of the constraint. */
	private String id;

	/** The scope of the constraint, i.e. the set of variables involved in the constraint. */
	public final Variable[] scp;

	/**
	 * The position of all variables of the problem in the constraint. It is -1 when not involved.For constraint of small arity, not necessarily built. So, you
	 * need to call <code> positionOf </code> instead of accessing directly this field.
	 */
	private int[] positions;

	public SetDense futvars;

	/** Indicates if the constraint must be ignored. */
	public boolean ignored;

	/** The key of the constraint. Used for symmetry detection. */
	public String key;

	/** The assistant which manages the tuples of the constraint. */
	public final TupleManager tupleManager;

	protected final Supporter supporter;

	/** Indicates if for each domain of a variable involved in the constraint, the index of any value corresponds to this value. */
	public final boolean indexesMatchValues;

	/** This field is used to store a tuple of (int) values. Is is inserted as a field in order to avoid overhead of memory allocations. */
	protected final int[] vals;

	public final Domain[] doms;

	public int cost = 1;

	public long timestamp;

	public int filteringComplexity;

	/**
	 * Indicates if filtering (e.g. GAC) must be controlled. If the number of uninstantiated variables is greater than this value, filtering is not achieved.
	 */
	public final int genericFilteringThreshold;

	public int nEffectiveFilterings;

	public Variable[] infiniteDomainVars;

	public SettingCtrs settings;

	/**********************************************************************************************
	 * General methods
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

	/**
	 * @return the position of the variable or <code>-1</code> if the variable is not involved in the constraint
	 */
	public final int positionOf(Variable x) {
		if (positions != null)
			return positions[x.num];
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
		int cnt = 0;
		for (Variable x : vars)
			if (involves(x))
				if (++cnt == scp.length)
					return true;
		return false;
	}

	/**
	 * Returns the weighted degree of the constraint.
	 */
	public final double wdeg() {
		return ((WdegVariant) ((SolverBacktrack) pb.solver).heuristicVars).cscores[num];
	}

	public boolean isIrreflexive() {
		control(scp.length == 2);
		int[] tuple = tupleManager.localTuple;
		int p = scp[0].dom.size() > scp[1].dom.size() ? 1 : 0, q = p == 0 ? 1 : 0;
		Domain dx = scp[p].dom, dy = scp[q].dom;
		for (int a = dx.first(); a != -1; a = dx.next(a)) {
			int b = dy.toIdx(dx.toVal(a));
			if (b < 0)
				continue;
			tuple[p] = a;
			tuple[q] = b;
			if (checkIndexes(tuple))
				return false;
		}
		return true;
	}

	public boolean isSubstitutableBy(int x, int a, int b) {
		tupleManager.firstValidTupleWith(x, a);
		return !tupleManager.findValidTupleSuchThat(t -> {
			t[x] = a;
			boolean b1 = checkIndexes(t);
			t[x] = b;
			boolean b2 = checkIndexes(t);
			return b1 && !b2;
		});
	}

	public boolean isGuaranteedAC() {
		if (this.infiniteDomainVars.length > 0)
			return false;
		if (this instanceof TagGACGuaranteed)
			return true;
		if (this instanceof TagGACUnguaranteed)
			return false;
		if (this instanceof FilteringSpecific)
			throw new UnsupportedOperationException(getClass().getName()); // to force the user to tag constraints or override the function
		else
			return genericFilteringThreshold == Integer.MAX_VALUE;
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

	public ExtensionStructure extStructure() {
		return null;
	}

	/**
	 * The assistant which manages information about the number of conflicts of the constraint.
	 */
	public ConflictsStructure conflictsStructure;

	// public final ConflictsStructure conflictsStructure() {
	// return conflictsStructure;
	// }

	public void cloneStructures(boolean onlyConflictsStructure) {
		if (conflictsStructure != null && conflictsStructure.registeredCtrs().size() > 1) {
			conflictsStructure.unregister(this);
			conflictsStructure = new ConflictsStructure(conflictsStructure, this);
		}
	}

	public void updateConflictsStructures(int[] frontier) {
		if (conflictsStructure != null && Stream.of(scp).anyMatch(x -> x.dom.lastRemoved() != frontier[x.num]) && !usePredefinedMaxNumberOfConflicts()) {
			if (conflictsStructure.registeredCtrs().size() > 1)
				cloneStructures(true);
			conflictsStructure.updateCounters(frontier);
		}
	}

	/**
	 * This function must be such that if (an upper bound of) the number of max conflicts is known for one pair (variable, index) then it is known for any pair
	 */
	public int giveUpperBoundOfMaxNumberOfConflictsFor(Variable x, int a) {
		return Resolution.UNDEFINED; // by default
	}

	/**
	 * we assume that if the number of max conflicts is known for one pair (variable, index) then it is known for any pair
	 */
	public boolean usePredefinedMaxNumberOfConflicts() {
		return giveUpperBoundOfMaxNumberOfConflictsFor(scp[0], scp[0].dom.first()) != Resolution.UNDEFINED;
	}

	/**********************************************************************************************
	 * Constructors
	 *********************************************************************************************/

	/**
	 * Private constructor just used to build the TAG constraint.
	 */
	private Constraint() {
		this.pb = null;
		this.scp = new Variable[0];
		this.tupleManager = null;
		this.vals = null;
		this.doms = null;
		this.genericFilteringThreshold = Integer.MAX_VALUE;
		this.indexesMatchValues = false;
		this.infiniteDomainVars = new Variable[0];
		this.supporter = null;
	}

	private final int computeGenericFilteringThreshold() {
		if (this instanceof FilteringSpecific || this instanceof Extension)
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

	public Constraint(Problem pb, Variable[] scp) {
		this.pb = pb;
		this.scp = scp = Stream.of(scp).distinct().toArray(Variable[]::new);
		control(scp.length >= 1 && Stream.of(scp).allMatch(x -> x != null), this + " with a scope badly formed ");
		Stream.of(scp).forEach(x -> x.collectedCtrs.add(this));
		this.infiniteDomainVars = Stream.of(scp).filter(x -> x.dom instanceof DomainInfinite).toArray(Variable[]::new);

		this.doms = Variable.buildDomainsArrayFor(scp);
		this.tupleManager = new TupleManager(scp);
		this.vals = new int[scp.length];
		this.settings = pb.rs.cp.settingCtrs;

		this.genericFilteringThreshold = computeGenericFilteringThreshold();
		this.indexesMatchValues = Stream.of(scp).allMatch(x -> x.dom.indexesMatchValues());

		if (this instanceof FilteringSpecific)
			pb.stuff.nSpecificCtrs++;
		if (this instanceof FilteringGlobal)
			pb.stuff.nGlobalCtrs++;
		if (this instanceof ObserverConstruction)
			pb.rs.observersConstruction.add(this);

		this.supporter = Supporter.buildFor(this);

		// if (pb.rs.cp.settingPropagation.residues && scp.length > 1 && !(this instanceof FilteringSpecific)
		// && !(pb.rs.cp.settingPropagation.classForRevisions.equals(Reviser3.class.getSimpleName()) && extStructure() instanceof Bits)) {
		// this.supporter = scp.length == 2 ? new SupporterHardBary(this) : new SupporterHardNary(this);
		// } else
		// this.supporter = null;
	}

	public final void reset() {
		control(futvars.free() == 0);
		nEffectiveFilterings = 0;
		timestamp = 0;
	}

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	public final void doPastVariable(Variable x) {
		if (positions != null)
			((SetSparse) futvars).remove(positions[x.num]);
		else
			for (int i = futvars.limit; i >= 0; i--) {
				if (scp[futvars.dense[i]] == x) {
					futvars.removeAtPosition(i);
					break;
				}
			}
	}

	public final void undoPastVariable(Variable x) {
		assert x.isAssigned() && scp[futvars.dense[futvars.size()]] == x;
		futvars.limit++;
	}

	/**
	 * Determines if the given tuple is a support of the constraint, i.e., if the given tuple belongs to the relation associated with the constraint. Be
	 * careful: although indexes of values are managed in the core of the solver, at this stage, the given tuple contains values (and not indexes of values).
	 * 
	 * @return true iff the tuple is a support of the constraint
	 */
	public abstract boolean checkValues(int[] t);

	/**
	 * Determines if the given tuple is a support of the constraint, i.e., if the given tuple belongs to the relation associated with the constraint. Be
	 * careful: the given tuple must contains indexes of values.
	 * 
	 * @param target
	 *            a given tuple of indexes (of values)
	 * @return true iff the tuple of values corresponding to the given tuple of indexes is a support of the constraint
	 */
	public boolean checkIndexes(int[] t) {
		return indexesMatchValues ? checkValues(t) : checkValues(toVals(t));
	}

	public int[] buildCurrentInstantiationTuple() {
		int[] tuple = tupleManager.localTuple;
		for (int i = tuple.length - 1; i >= 0; i--)
			tuple[i] = doms[i].unique();
		return tuple;
	}

	/** All variables of the scope must be fixed. */
	public boolean checkCurrentInstantiation() {
		return checkIndexes(buildCurrentInstantiationTuple());
	}

	public long costOfIdxs(int[] idxs) {
		return checkIndexes(idxs) ? 0 : cost;
	}

	public long costOfCurrInstantiation() {
		return costOfIdxs(buildCurrentInstantiationTuple());
	}

	/**
	 * Transforms all indexes of the given tuple into values. Elements of the tuple must then correspond to index of values occurring in the domains of the
	 * variables involved in the constraint.
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
	 * Determines if the given tuple (usually a support) is still valid. We have just to test that all indexes are still in the domains of the variables
	 * involved in the constraint. Do not call the <code> check </code> method instead since it can not take into account removed values.
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

	/**
	 * Seeks a support for the constraint when considering the current state of the domains and the tuple currently managed by the tuple manager (initial value
	 * of the current tuple included in search). A lexicographic order is used.
	 */
	private final boolean seekSupport() {
		return tupleManager.findValidTupleSuchThat(t -> checkIndexes(t));
	}

	public final boolean seekFirstSupport() {
		tupleManager.firstValidTuple();
		return seekSupport();
	}

	public final boolean seekFirstSupport(int[] buffer) {
		tupleManager.firstValidTuple(buffer);
		return seekSupport();
	}

	public final boolean seekFirstSupportWith(int x, int a) {
		tupleManager.firstValidTupleWith(x, a);
		return seekSupport();
	}

	public boolean seekFirstSupportWith(int x, int a, int[] buffer) {
		tupleManager.firstValidTupleWith(x, a, buffer);
		return seekSupport();
	}

	public final boolean seekFirstSupportWith(int x, int a, int y, int b) {
		tupleManager.firstValidTupleWith(x, a, y, b);
		return seekSupport();
	}

	public final boolean seekFirstSupportWith(int x, int a, int y, int b, int[] buffer) {
		tupleManager.firstValidTupleWith(x, a, y, b, buffer);
		return seekSupport();
	}

	// The next support is searched for from tupleManager.currTuple(), excluded, which is not necessarily valid (as it may have been
	// deleted). If some values have been fixed, they remain fixed
	public final boolean seekNextSupport() {
		return tupleManager.nextValidTupleCautiously() != -1 && seekSupport();
	}

	private final boolean seekConflict() {
		return tupleManager.findValidTupleSuchThat(t -> !checkIndexes(t));
		// assert tupleManager.currTuple() == inoutTuple;
		// // assert checkValidityOf(inoutTuple); // A REMETREet A ENLEVR POUR ?????
		// while (true)
		// if (!checkIndexes(inoutTuple))
		// return true;
		// else if (tupleManager.nextValidTuple() == -1)
		// return false;
	}

	public final boolean seekFirstConflict() {
		tupleManager.firstValidTuple();
		return seekConflict();
	}

	public final boolean seekFirstConflictWith(int x, int a) {
		tupleManager.firstValidTupleWith(x, a);
		return seekConflict();
	}

	public long nSupports() {
		tupleManager.firstValidTuple();
		return tupleManager.countValidTuplesSuchThat(t -> checkIndexes(t));
	}

	public long nConflicts() {
		tupleManager.firstValidTuple();
		return tupleManager.countValidTuplesSuchThat(t -> !checkIndexes(t));
	}

	public long nSupportsFor(int x, int a) {
		tupleManager.firstValidTupleWith(x, a);
		return tupleManager.countValidTuplesSuchThat(t -> checkIndexes(t));
	}

	public long nConflictsFor(int x, int a) {
		tupleManager.firstValidTupleWith(x, a);
		return tupleManager.countValidTuplesSuchThat(t -> !checkIndexes(t));
	}

	public boolean findArcSupportFor(int x, int a) {
		if (supporter != null)
			return ((SupporterHard) supporter).findArcSupportFor(x, a);
		if (extStructure() instanceof Bits) {
			long[] t1 = ((Bits) extStructure()).bitSupsFor(x)[a];
			long[] t2 = scp[x == 0 ? 1 : 0].dom.binaryRepresentation();
			for (int i = 0; i < t1.length; i++) {
				if ((t1[i] & t2[i]) != 0)
					return true;
			}
			return false;
		}
		// AC3 below
		return seekFirstSupportWith(x, a);
	}

	/**
	 * We assume that the given array corresponds to a tuple of indexes (and not to a tuple of values).
	 * 
	 * @param idxs
	 *            the tuple to be removed
	 */
	public boolean removeTuple(int... idxs) {
		throw new AssertionError();
	}

	/**********************************************************************************************
	 * Methods related to filtering
	 *********************************************************************************************/

	private boolean genericFiltering(Variable x) {
		Reviser reviser = ((Forward) pb.solver.propagation).reviser;
		if (x.isAssigned()) {
			for (int i = futvars.limit; i >= 0; i--)
				if (reviser.revise(this, scp[futvars.dense[i]]) == false)
					return false;
		} else {
			boolean revisingEventVarToo = (scp.length == 1); // TODO can we just initialize it to false ?
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y == x)
					continue;
				if (timestamp < y.timestamp)
					revisingEventVarToo = true;
				if (reviser.revise(this, y) == false)
					return false;
			}
			if (revisingEventVarToo && reviser.revise(this, x) == false)
				return false;
		}
		return true;
	}

	private void handleEffectiveFilterings() {
		if (pb.solver instanceof SolverBacktrack)
			((SolverBacktrack) pb.solver).proofer.updateProof(this);// TODO // ((SystematicSolver)solver).updateProofAll();
		nEffectiveFilterings++;
		pb.stuff.nEffectiveFilterings++;
	}

	private boolean completeFilteringAtEachCall() {
		if (this instanceof TagFilteringCompleteAtEachCall)
			return true;
		if (this instanceof TagFilteringPartialAtEachCall)
			return false;
		throw new UnsupportedOperationException(getClass().getName()); // to force the user to tag constraints or override the function
	}

	private Boolean handleHugeDomains() {
		assert infiniteDomainVars.length > 0;
		// TODO huge domains are not finalized
		if (futvars.size() == 0)
			return this.checkCurrentInstantiation();
		if (futvars.size() == 1) {
			if (this instanceof SumSimpleEQ) {
				((SumSimpleEQ) this).deduce();
				return true;
			}
			if (this instanceof SumWeightedEQ) {
				((SumWeightedEQ) this).deduce();
				return true;
			}
		}
		// for (Variable y : hugeDomainVars)
		// if (!y.isAssigned())
		// return true; // we have to wait
		if (futvars.size() > 0)
			return true;
		return null;
	}

	/**
	 * This is the method that is called for filtering. We know that the domain of the specified variable has been recently reduced, but this is not necessarily
	 * the only one in that situation.
	 */
	public final boolean filterFrom(Variable x) {
		// System.out.println("filtering " + this + " " + x);

		if (this.infiniteDomainVars.length > 0) {
			Boolean b = handleHugeDomains();
			if (b != null)
				return b;
		}

		// For CSP, there are first some conditions that allow us to directly return true (because we know then that there is no filtering
		// possibility)
		if (pb.settings.framework == TypeFramework.CSP) { // if != MACSP, pb with java -ea ac PlaneparkingTask.xml -ea -cm=false -ev -trace
															// possibly too with GraphColoring-sum-GraphColoring_1-fullins-3.xml.lzma
			if (futvars.size() == 0) {
				if (isGuaranteedAC()) {
					assert checkCurrentInstantiation() : "Unsatisfied constraint " + this;
					return true;
				} else
					return checkCurrentInstantiation();
			}
			if (futvars.size() == 1 && x.isFuture() && scp.length > 1)
				return true;
		}
		int nBefore = pb.nValuesRemoved;
		boolean consistent = true;
		if (this instanceof FilteringSpecific) {
			if (timestamp > x.timestamp && completeFilteringAtEachCall())
				return true;
			consistent = ((FilteringSpecific) this).runPropagator(x);
		} else {
			if (timestamp > x.timestamp || futvars.size() > genericFilteringThreshold)
				return true;
			consistent = genericFiltering(x);
		}
		if (!consistent || pb.nValuesRemoved != nBefore)
			this.handleEffectiveFilterings();
		timestamp = pb.solver.propagation.incrementTime();
		return consistent;
	}

	public boolean controlArcConsistency() {
		if (ignored)
			return true;
		if (Variable.nValidTuplesBoundedAtMaxValueFor(scp) > 1000)
			return true;
		for (int i = 0; i < scp.length; i++)
			for (int a = doms[i].first(); a != -1; a = doms[i].next(a))
				if (seekFirstSupportWith(i, a) == false) {
					Kit.log.warning(" " + scp[i] + "=" + a + " not supported by " + this);
					display(true);
					return false;
				}
		return true;
	}

	/**********************************************************************************************
	 * Control and display
	 *********************************************************************************************/

	public void control(boolean conditionToBeRespected, String message) {
		Utilities.control(conditionToBeRespected, message);
	}

	public void control(boolean conditionToBeRespected) {
		Utilities.control(conditionToBeRespected, "");
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
		Kit.log.finer(
				"\tClass = " + getClass().getName() + (this instanceof Extension ? ":" + ((Extension) this).extStructure().getClass().getSimpleName() : ""));
		if (this instanceof Intension)
			Kit.log.finer("\tPredicate: " + ((Intension) this).tree.toFunctionalExpression(null));
		Kit.log.finer("\tKey = " + key);
		int[] t = getSymmetryMatching(key);
		Kit.log.finest("\tSymmetryMatching = " + (t == null ? " undefined " : Kit.join(t)));
		Kit.log.finest("\tCost = " + cost);
		// Kit.log.finer("\tXCSP = " + defXCSP());
	}

	protected String compact(Variable[] vars) {
		return pb.varEntities.compact(vars);
	}

	protected String compactOrdered(Variable[] vars) {
		return pb.varEntities.compactOrdered(vars);
	}

}
