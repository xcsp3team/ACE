/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problem;

import static dashboard.Output.ARITIES;
import static dashboard.Output.DEFAULT_COSTS;
import static dashboard.Output.MEM;
import static dashboard.Output.NAME;
import static dashboard.Output.NUMBER;
import static dashboard.Output.N_CLIQUES;
import static dashboard.Output.N_SHARED_BINARY_REPRESENTATIONS;
import static dashboard.Output.TABLES;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeOptimization;
import org.xcsp.common.predicates.TreeEvaluator.ExternFunctionArity1;
import org.xcsp.common.predicates.TreeEvaluator.ExternFunctionArity2;

import constraints.Constraint;
import constraints.extension.Extension;
import constraints.extension.ExtensionSmart;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableSmart;
import constraints.intension.Intension;
import dashboard.Arguments;
import dashboard.Control.SettingVars;
import dashboard.Output;
import sets.SetDense;
import utility.Kit;
import variables.Variable;

public final class ProblemStuff {

	/**********************************************************************************************
	 * Repartitioner
	 *********************************************************************************************/

	public static class Repartitioner<T extends Comparable<? super T>> {

		private final static int DEFAULT_MAX_VALUE = 8;

		private final int maxElementsToDisplay;

		/** For each key, the number of occurrences is recorded (as value). */
		private final Map<T, Integer> repartition = new HashMap<>();

		/** Sorted keys, when the repartition has been frozen. */
		private List<T> sortedKeys;

		public void add(T value) {
			if (sortedKeys != null)
				sortedKeys = null; // to start a new repartition
			Integer nb = repartition.get(value);
			repartition.put(value, nb == null ? 1 : nb + 1);
		}

		private void freeze() {
			Kit.control(sortedKeys == null);
			Collections.sort(sortedKeys = new ArrayList<T>(repartition.keySet()));
		}

		public T first() {
			if (sortedKeys == null)
				freeze();
			return sortedKeys.size() == 0 ? null : sortedKeys.get(0);
		}

		public T last() {
			if (sortedKeys == null)
				freeze();
			return sortedKeys.size() == 0 ? null : sortedKeys.get(sortedKeys.size() - 1);
		}

		public int size() {
			return repartition.size();
		}

		private Repartitioner(int maxElementsToDisplay) {
			this.maxElementsToDisplay = maxElementsToDisplay;
		}

		public Repartitioner(boolean verbose) {
			this(verbose ? Integer.MAX_VALUE : DEFAULT_MAX_VALUE);
		}

		public Repartitioner() {
			this(DEFAULT_MAX_VALUE);
		}

		/** Only valid for repartition of values (when keys are integers too). */
		public long cumulatedSum() {
			return repartition.entrySet().stream().mapToLong(e -> e.getValue() * (Integer) e.getKey()).sum();
		}

		@Override
		public String toString() {
			if (sortedKeys == null)
				freeze();
			String SEP = "#", JOIN = ",";
			if (sortedKeys.size() <= maxElementsToDisplay)
				return "[" + sortedKeys.stream().map(k -> k + SEP + repartition.get(k)).collect(Collectors.joining(JOIN)) + "]";
			else {
				String s1 = IntStream.range(0, DEFAULT_MAX_VALUE / 2).mapToObj(i -> sortedKeys.get(i) + SEP + repartition.get(sortedKeys.get(i)))
						.collect(Collectors.joining(JOIN));
				String s2 = IntStream.range(sortedKeys.size() - DEFAULT_MAX_VALUE / 2, sortedKeys.size())
						.mapToObj(i -> sortedKeys.get(i) + SEP + repartition.get(sortedKeys.get(i))).collect(Collectors.joining(JOIN));
				return "[" + s1 + "..." + s2 + "]";
			}
		}
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	private final Problem problem;

	/** The variables that have been collected so far. */
	public final List<Variable> collectedVarsAtInit = new ArrayList<>();

	/** The constraints that have been collected so far. */
	public final List<Constraint> collectedCtrsAtInit = new ArrayList<>();

	public final Map<String, String> collectedTuples = new HashMap<>();

	protected final Repartitioner<Integer> varDegrees, domSizes, ctrArities, tableSizes;
	protected final Repartitioner<Long> defaultCosts;
	protected final Repartitioner<String> ctrTypes;

	/**
	 * The number of distinct relations (ie. types of relation) used by the constraints of the problem. <br>
	 * It is equal to <code> -1 </code> when it is unknown.
	 */
	public int nIsolatedVars, nFixedVars;
	public int nRemovedUnaryCtrs, nConvertedConstraints; // conversion intension to extension
	public int nSpecificCtrs, nMergedCtrs, nDiscardedCtrs, nAddedCtrs, nUniversalCtrs;

	public long nEffectiveFilterings;

	public int nSharedBinaryRepresentations;

	public int nFilterCallsSTR;
	public double sumTableProportionsSTR, sumTableSizesSTR;

	private Map<String, String> mapForAutomorphismIdentification = new LinkedHashMap<>();
	private Map<String, String> mapForAllDifferentIdentification = new LinkedHashMap<>();

	public ExternFunctionArity1 externFunctionArity1;
	public ExternFunctionArity2 externFunctionArity2;

	public int nValuesRemovedAtConstructionTime; // sum over all variable domains

	private Set<String> discardedVars = new HashSet<>(); // ids of discarded variables
	Set<String> discardedScps = new HashSet<>();

	public final boolean mustDiscard(IVar x) {
		Object[] selectedVars = problem.head.control.variables.selectedVars;
		if (selectedVars.length == 0)
			return false;
		int num = collectedVarsAtInit.size() + discardedVars.size();
		boolean mustDiscard = Arrays.binarySearch(selectedVars, selectedVars[0] instanceof Integer ? num : x.id()) < 0;
		if (mustDiscard)
			discardedVars.add(x.id());
		return mustDiscard;
	}

	public final boolean mustDiscard(IVar[] scp) {
		if (problem.head.control.variables.selectedVars.length == 0)
			return false;
		boolean mustDiscard = Stream.of(scp).map(x -> x.id()).anyMatch(id -> discardedVars.contains(id));
		if (mustDiscard)
			nDiscardedCtrs++;
		return mustDiscard;
	}

	public static class StuffOptimization {
		// public List<FunctionalPropagator> collectedCostVarsFunctionalPropagatorsAtInit = new ArrayList<>();

		public Collection<Variable[][]> collectedSatPreservingPermutationsAtInit = new ArrayList<>();

		public boolean areIndependantPermutationSets;

		// public void addCostVarDefinition(Variable var, CtrHard ctr) {
		// FunctionalPropagator propagator = FunctionalPropagator.buildFunctionalPropagator(ctr, ctr.positionOf(var));
		// collectedCostVarsFunctionalPropagatorsAtInit.add(propagator);
		// }
	}

	public StuffOptimization stuffOptimization = new StuffOptimization();

	/**********************************************************************************************
	 * Methods for conflicts structures
	 *********************************************************************************************/

	private boolean controlConstraintsOfConflictStructures() {
		Stream.of(problem.constraints).forEach(c -> Kit.control(c.conflictsStructure == null || c.conflictsStructure.registeredCtrs().contains(c),
				() -> "pb cloneConstraitnStructure " + c + " " + c.conflictsStructure.firstRegisteredCtr()));
		return true;
	}

	private boolean controlUnitListsOfConflictStructures() {
		Stream.of(problem.constraints).filter(c -> c.conflictsStructure != null)
				.forEach(c -> Kit.control(c.conflictsStructure.registeredCtrs().contains(c) && c.conflictsStructure.registeredCtrs().size() == 1,
						() -> "pb cloneConstraitnStructure " + c + " " + c.conflictsStructure.firstRegisteredCtr()));
		return true;
	}

	public void cloneStructuresOfConstraintsWithArity(int arity, boolean onlyConflictsStructure) {
		assert controlConstraintsOfConflictStructures();
		Kit.log.info("   Before cloning, mem=" + Kit.memoryInMb());
		Stream.of(problem.constraints).filter(c -> arity == -1 || c.scp.length == arity).forEach(c -> c.cloneStructures(onlyConflictsStructure));
		Kit.log.info("   After cloning, mem=" + Kit.memoryInMb());
		assert controlUnitListsOfConflictStructures();
	}

	public void cloneStructuresOfConstraints(boolean onlyConflictsStructure) {
		cloneStructuresOfConstraintsWithArity(-1, onlyConflictsStructure);
	}

	/**********************************************************************************************
	 * Methods for metrics
	 *********************************************************************************************/

	public int nDomTypes() {
		return (int) Stream.of(problem.variables).mapToInt(x -> x.dom.typeIdentifier()).distinct().count();
	}

	private void printNumber(int n) {
		if (problem.head.control.general.verbose > 1) {
			int nDigits = (int) Math.log10(n) + 1;
			IntStream.range(0, nDigits).forEach(i -> System.out.print("\b")); // we need to discard previous characters
			System.out.print((n + 1) + "");
		}
	}

	public final int addCollectedVariable(Variable x) {
		if (collectedVarsAtInit.isEmpty()) // first call
			System.out.print(Output.COMMENT_PREFIX + "Loading variables...");
		printNumber(collectedVarsAtInit.size());

		int num = collectedVarsAtInit.size();
		collectedVarsAtInit.add(x);
		domSizes.add(x.dom.initSize());
		return num;
	}

	public final int addCollectedConstraint(Constraint c) {
		if (collectedCtrsAtInit.isEmpty()) // first call
			System.out.println("\n" + Output.COMMENT_PREFIX + "Loading constraints...");
		printNumber(collectedCtrsAtInit.size());

		int num = collectedCtrsAtInit.size();
		collectedCtrsAtInit.add(c);
		ctrArities.add(c.scp.length);
		if (c.scp.length == 1) {
			if (c instanceof Extension || c instanceof Intension)
				ctrTypes.add(c.getClass().getSimpleName() + "1");
			// else
			// throw new UnreachableCodeException();
		} else
			ctrTypes.add(c.getClass().getSimpleName() + (c instanceof Extension ? "-" + ((Extension) c).extStructure().getClass().getSimpleName() : ""));
		if (c instanceof ExtensionSmart)
			tableSizes.add(((TableSmart) ((Extension) c).extStructure()).smartTuples.length);
		if (c instanceof Extension && ((Extension) c).extStructure() instanceof Table)
			tableSizes.add(((Table) ((Extension) c).extStructure()).tuples.length);
		return num;
	}

	public int maxDomSize() {
		return domSizes.last();
	}

	public int maxVarDegree() {
		return varDegrees.last();
	}

	public int minCtrArity() {
		return ctrArities.first();
	}

	public int maxCtrArity() {
		return ctrArities.last();
	}

	protected ProblemStuff(Problem problem) {
		this.problem = problem;
		boolean verbose = problem.head.control.general.verbose > 1;
		this.varDegrees = new Repartitioner<>(verbose);
		this.domSizes = new Repartitioner<>(verbose);
		this.ctrArities = new Repartitioner<>(verbose);
		this.ctrTypes = new Repartitioner<>(true);
		this.tableSizes = new Repartitioner<>(verbose);
		this.defaultCosts = new Repartitioner<>(verbose);
	}

	public void updateStatsForSTR(SetDense set) {
		nFilterCallsSTR++;
		if (set != null) {
			sumTableProportionsSTR += set.limit / (double) set.capacity();
			sumTableSizesSTR += set.limit;
		}
	}

	public boolean hasSharedExtensionStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.extStructure() != null && c.extStructure().firstRegisteredCtr() != c);
	}

	public boolean hasSharedConflictsStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.conflictsStructure != null && c.conflictsStructure.firstRegisteredCtr() != c);
	}

	protected void addToMapForAutomorphismIdentification(IdentificationAutomorphism automorphismIdentification) {
		automorphismIdentification.putInMap(mapForAutomorphismIdentification);
	}

	protected void addToMapForAllDifferentIdentification(IdentificationAllDifferent allDifferentIdentification) {
		mapForAllDifferentIdentification.put(N_CLIQUES, allDifferentIdentification.nBuiltCliques + "");
	}

	/**********************************************************************************************
	 * Methods for maps
	 *********************************************************************************************/

	public static class MapAtt {

		public static final String SEPARATOR = "separator";

		private String name;

		private List<Entry<String, Object>> entries = new ArrayList<>();

		public MapAtt(String name) {
			this.name = name;
		}

		public MapAtt putIf(String key, Object value, boolean condition, boolean separation) {
			if (condition) {
				if (separation)
					separator();
				entries.add(new SimpleEntry<>(key, value));
			}
			return this;
		}

		public MapAtt putIf(String key, Object value, boolean condition) {
			return putIf(key, value, condition, false);
		}

		public MapAtt putWhenPositive(String key, Number value) {
			return putIf(key, value, value.doubleValue() > 0);
		}

		public MapAtt put(String key, Object value) {
			return putIf(key, value, true);
		}

		public MapAtt separator() {
			return putIf(SEPARATOR, null, true);
		}

		public List<Entry<String, Object>> entries() {
			return entries.stream().filter(e -> e.getKey() != SEPARATOR).collect(Collectors.toCollection(ArrayList::new));
		}

		@Override
		public String toString() {
			String s = (name.equals("Run") ? "" : Output.COMMENT_PREFIX + Kit.preprint(name, Kit.BLUE) + "\n") + Output.COMMENT_PREFIX + Output.COMMENT_PREFIX;
			boolean sep = true;
			for (int i = 0; i < entries.size(); i++) {
				Entry<String, Object> e = entries.get(i);
				if (e.getKey() == SEPARATOR) {
					s += "\n" + Output.COMMENT_PREFIX + Output.COMMENT_PREFIX;
					sep = true;
				} else {
					if (!sep)
						s += "  ";
					s += (e.getKey() + "=" + e.getValue());
					sep = false;
				}
			}
			return s;
		}
	}

	public MapAtt instanceAttributes(int instanceNumber) {
		MapAtt m = new MapAtt("Instance");
		m.put(NAME, problem.name());
		m.putIf(NUMBER, instanceNumber, Arguments.nInstancesToSolve > 1);
		SettingVars settings = problem.head.control.variables;
		if (settings.selectedVars.length > 0 || settings.instantiatedVars.length > 0 || settings.priorityVars.length > 0) {
			m.separator();
			m.putIf("selection", Stream.of(settings.selectedVars).map(o -> o.toString()).collect(Collectors.joining(",")), settings.selectedVars.length > 0);
			m.putIf("instantiation", IntStream.range(0, settings.instantiatedVars.length)
					.mapToObj(i -> settings.instantiatedVars[i] + "=" + settings.instantiatedVals[i]).collect(Collectors.joining(",")),
					settings.instantiatedVars.length > 0);
			m.putIf("priority", Stream.of(settings.priorityVars).map(o -> o.toString()).collect(Collectors.joining(",")), settings.priorityVars.length > 0);
			m.putWhenPositive("nStrictPriorityVars", settings.nStrictPriorityVars);
		}
		return m;
	}

	public MapAtt domainsAttributes() {
		MapAtt m = new MapAtt("Domains");
		m.put("nTypes", nDomTypes());
		m.put("nValues", Variable.nValidValuesFor(problem.variables));
		m.putWhenPositive("nRemovedValuesAtConstruction", nValuesRemovedAtConstructionTime);
		m.putWhenPositive("nPurged", problem.nValuesRemoved);
		m.put("sizes", domSizes);
		return m;
	}

	public MapAtt variablesAttributes() {
		MapAtt m = new MapAtt("Variables");
		m.put("count", problem.variables.length);
		m.putWhenPositive("nDiscarded", discardedVars.size());
		m.putWhenPositive("nIsolated", nIsolatedVars);
		m.putWhenPositive("nFixed", nFixedVars);
		m.put("degrees", varDegrees);
		return m;
	}

	public MapAtt ctrsAttributes() {
		MapAtt m = new MapAtt("Constraints");
		m.put("count", problem.constraints.length);
		m.putWhenPositive("nRemovedUnary", nRemovedUnaryCtrs);
		m.putWhenPositive("nConverted", nConvertedConstraints);
		m.putWhenPositive("nSpecific", nSpecificCtrs);
		m.putWhenPositive("nMerged", nMergedCtrs);
		m.putWhenPositive("nDiscarded", nDiscardedCtrs);
		m.putWhenPositive("nAdded", nAddedCtrs);
		m.putWhenPositive("nUniversal", nUniversalCtrs);
		m.put(ARITIES, ctrArities);
		m.putIf("distribution", ctrTypes, true, true);
		if (tableSizes.repartition.size() > 0) {
			m.separator();
			m.put(TABLES, tableSizes);
			m.putIf(DEFAULT_COSTS, defaultCosts.toString(), defaultCosts.repartition.size() > 0);
			m.put("nTotalTuples", tableSizes.cumulatedSum());
		}
		m.putIf("automorphism", mapForAutomorphismIdentification.entrySet().stream().map(e -> e.getKey() + ":" + e.getValue()).collect(Collectors.joining(" ")),
				mapForAutomorphismIdentification.size() > 0, true);
		m.putIf("alldiffIdent", mapForAllDifferentIdentification.entrySet().stream().map(e -> e.getKey() + ":" + e.getValue()).collect(Collectors.joining(" ")),
				mapForAllDifferentIdentification.size() > 0, true);
		int nConflictsStructures = 0, nSharedConflictsStructures = 0, nUnbuiltConflictsStructures = 0;
		int nExtensionStructures = 0, nSharedExtensionStructures = 0, nEvaluationManagers = 0, nSharedEvaluationManagers = 0;
		for (Constraint c : problem.constraints) {
			if (c instanceof Extension)
				if (c.extStructure().firstRegisteredCtr() == c)
					nExtensionStructures++;
				else
					nSharedExtensionStructures++;
			if (c instanceof Intension)
				if (((Intension) c).treeEvaluator.firstRegisteredCtr() == c)
					nEvaluationManagers++;
				else
					nSharedEvaluationManagers++;
			if (c.conflictsStructure == null)
				nUnbuiltConflictsStructures++;
			else if (c.conflictsStructure.firstRegisteredCtr() == c)
				nConflictsStructures++;
			else
				nSharedConflictsStructures++;
		}
		if (nExtensionStructures > 0 || nEvaluationManagers > 0 || nConflictsStructures > 0 || nSharedBinaryRepresentations > 0) {
			m.separator();
			m.putIf("nExtStructures", "(" + nExtensionStructures + ",shared:" + nSharedExtensionStructures + ")", nExtensionStructures > 0);
			m.putIf("nIntStructures", "(" + nEvaluationManagers + ",shared:" + nSharedEvaluationManagers + ")", nEvaluationManagers > 0);
			m.putIf("nCftStructures", "(" + nConflictsStructures + ",shared:" + nSharedConflictsStructures
					+ (nUnbuiltConflictsStructures > 0 ? ",unbuilt:" + nUnbuiltConflictsStructures : "") + ")", nConflictsStructures > 0);
			m.putWhenPositive(N_SHARED_BINARY_REPRESENTATIONS, nSharedBinaryRepresentations);
		}
		m.separator();
		m.put("wck", problem.head.instanceStopwatch.wckTimeInSeconds());
		m.put("cpu", problem.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		// m.putPositive( COMPRESSION, TableCompressed3.compression);
		return m;
	}

	public MapAtt objsAttributes() {
		MapAtt m = new MapAtt("Objective");
		m.put("way", (problem.optimizer.minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName());
		Kit.control(problem.optimizer.ctr != null);
		m.put("type", problem.optimizer.ctr.getClass().getSimpleName());
		m.put("bounds", (problem.optimizer.clb.limit() + ".." + problem.optimizer.cub.limit()));
		return m;
	}

}
