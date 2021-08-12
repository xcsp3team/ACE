package problem;

import static dashboard.Output.ARITIES;
import static dashboard.Output.BOUNDS;
import static dashboard.Output.CONSTRAINTS;
import static dashboard.Output.COUNT;
import static dashboard.Output.CPU;
import static dashboard.Output.DEGREES;
import static dashboard.Output.DISTRIBUTION;
import static dashboard.Output.DOMAINS;
import static dashboard.Output.INSTANCE;
import static dashboard.Output.INSTANTIATION;
import static dashboard.Output.MEM;
import static dashboard.Output.NAME;
import static dashboard.Output.NUMBER;
import static dashboard.Output.N_ADDED;
import static dashboard.Output.N_AUXILIARY;
import static dashboard.Output.N_CFT_STRUCTURES;
import static dashboard.Output.N_CLIQUES;
import static dashboard.Output.N_CONVERTED;
import static dashboard.Output.N_DELETED;
import static dashboard.Output.N_DISCARDED;
import static dashboard.Output.N_EXT_STRUCTURES;
import static dashboard.Output.N_FIXED;
import static dashboard.Output.N_GENERATORS;
import static dashboard.Output.N_INT_STRUCTURES;
import static dashboard.Output.N_ISOLATED;
import static dashboard.Output.N_MERGED;
import static dashboard.Output.N_REMOVED1;
import static dashboard.Output.N_SPECIFIC;
import static dashboard.Output.N_STRICT_PRIORITY;
import static dashboard.Output.N_SYMBOLIC;
import static dashboard.Output.N_TUPLES;
import static dashboard.Output.N_TYPES;
import static dashboard.Output.N_VALUES;
import static dashboard.Output.OBJECTIVE;
import static dashboard.Output.PRIORITY;
import static dashboard.Output.RUN;
import static dashboard.Output.SELECTION;
import static dashboard.Output.SHARED_BITS;
import static dashboard.Output.SIZES;
import static dashboard.Output.TABLES;
import static dashboard.Output.TYPE;
import static dashboard.Output.VARIABLES;
import static dashboard.Output.WAY;
import static dashboard.Output.WCK;
import static java.util.stream.Collectors.joining;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
import org.xcsp.parser.entries.XConstraints.XCtr;
import org.xcsp.parser.entries.XObjectives.XObj;

import constraints.Constraint;
import constraints.extension.CSmart;
import constraints.extension.Extension;
import constraints.extension.Extension.Extension1;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableSmart;
import constraints.intension.Intension;
import dashboard.Control.SettingVars;
import dashboard.Input;
import dashboard.Output;
import utility.Kit;
import variables.Variable;

/**
 * This class stores some information (features) about the problem (constraint network).
 * 
 * @author Christophe Lecoutre
 */
public final class Features {

	/**********************************************************************************************
	 * Auxiliary Class Repartitioner
	 *********************************************************************************************/

	/**
	 * An object of this class allows us to record the number of occurrences of some objects (of type T).
	 */
	public static class Repartitioner<T extends Comparable<? super T>> {

		private final static int DEFAULT_MAX_VALUE = 8;

		private final int maxElementsToDisplay;

		/**
		 * For each key, the number of occurrences is recorded (as value).
		 */
		private final Map<T, Integer> repartition = new HashMap<>();

		/**
		 * Sorted keys, when the repartition has been frozen.
		 */
		private List<T> sortedKeys;

		/**
		 * Adds an element (key) to the repartitioner. If this is the first occurrence, it is recorded with associated counter 1. Otherwise, its associated
		 * counter is incremented by 1.
		 * 
		 * @param key
		 *            the specified key to consider
		 */
		public void add(T key) {
			if (sortedKeys != null)
				sortedKeys = null; // to start a new repartition
			Integer nb = repartition.get(key);
			repartition.put(key, nb == null ? 1 : nb + 1);
		}

		/**
		 * Freeze the repartition. This corresponds to sort the keys. Then, we can make some requests (e.g., getting the value of the first sorted key).
		 */
		private void freeze() {
			Kit.control(sortedKeys == null);
			Collections.sort(sortedKeys = new ArrayList<T>(repartition.keySet()));
		}

		/**
		 * Returns the first key after keys have been sorted
		 * 
		 * @return the first key after keys have been sorted
		 */
		public T first() {
			if (sortedKeys == null)
				freeze();
			return sortedKeys.size() == 0 ? null : sortedKeys.get(0);
		}

		/**
		 * Returns the last key after keys have been sorted
		 * 
		 * @return the last key after keys have been sorted
		 */
		public T last() {
			if (sortedKeys == null)
				freeze();
			return sortedKeys.size() == 0 ? null : sortedKeys.get(sortedKeys.size() - 1);
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

		@Override
		public String toString() {
			if (repartition.size() == 0)
				return "";
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
	 * Auxiliary Class Collecting : to store (at construction time) variables and constraints (and also table keys)
	 *********************************************************************************************/

	/**
	 * This class allows us to collect variables and constraints when loading the constraitn network.
	 */
	public final class Collecting {

		/**
		 * The variables that have been collected so far
		 */
		public final List<Variable> variables = new ArrayList<>();

		/**
		 * The constraints that have been collected so far
		 */
		public final List<Constraint> constraints = new ArrayList<>();

		/**
		 * The keys used for tables, that have been collected so far, and used when storing tuples of a table constraint. Relevant only for symmetry-breaking.
		 */
		public final Map<String, String> tableKeys = new HashMap<>();

		/**
		 * Ids of discarded variables
		 */
		private Set<String> discardedVars = new HashSet<>();

		/**
		 * Returns true if the specified variable must be discarded
		 * 
		 * @param x
		 *            a variable
		 * @return true if the specified variable must be discarded
		 */
		private boolean mustDiscard(IVar x) {
			Object[] selectedVars = problem.head.control.variables.selectedVars;
			if (selectedVars.length == 0)
				return false;
			int num = collecting.variables.size() + discardedVars.size();
			boolean mustDiscard = Arrays.binarySearch(selectedVars, selectedVars[0] instanceof Integer ? num : x.id()) < 0;
			if (mustDiscard)
				discardedVars.add(x.id());
			return mustDiscard;
		}

		private boolean mustDiscard(IVar[] scp) {
			if (problem.head.control.variables.selectedVars.length == 0)
				return false;
			boolean mustDiscard = Stream.of(scp).map(x -> x.id()).anyMatch(id -> discardedVars.contains(id));
			if (mustDiscard)
				nDiscardedCtrs++;
			return mustDiscard;
		}

		/**
		 * Returns true if the specified constraint must be discarded
		 * 
		 * @param c
		 *            a constraint
		 * @return true if the specified constraint must be discarded
		 */
		public final boolean mustDiscard(XCtr c) {
			if (mustDiscard(c.vars()))
				return true;
			boolean mustDiscard = problem.head.control.constraints.ignoredCtrType == c.type
					|| problem.head.control.constraints.ignoreCtrArity == c.vars().length;
			if (mustDiscard)
				nDiscardedCtrs++;
			return mustDiscard;
		}

		/**
		 * Returns true if the specified objective must be discarded
		 * 
		 * @param o
		 *            an objective
		 * @return true if the specified objective must be discarded
		 */
		public final boolean mustDiscard(XObj o) {
			return mustDiscard(o.vars());
		}

		private void printNumber(int n) {
			if (problem.head.control.general.verbose > 1) {
				int nDigits = (int) Math.log10(n) + 1;
				IntStream.range(0, nDigits).forEach(i -> System.out.print("\b")); // we need to discard previous characters
				System.out.print((n + 1) + "");
			}
		}

		/**
		 * Add the specified variable to those that have been already collected
		 * 
		 * @param x
		 *            a variable
		 * @return the num(ber) of the variable
		 */
		public int add(Variable x) {
			if (mustDiscard(x))
				return -1;
			if (variables.isEmpty()) // first call
				System.out.print(Output.COMMENT_PREFIX + "Loading variables...");
			int num = variables.size();
			printNumber(num);
			variables.add(x);
			domSizes.add(x.dom.initSize());
			return num;
		}

		/**
		 * Add the specified constraint to those that have been already collected
		 * 
		 * @param c
		 *            a constraint
		 * @return the num(ber) of the constraint
		 */
		public int add(Constraint c) {
			if (constraints.isEmpty()) // first call
				System.out.println("\n" + Output.COMMENT_PREFIX + "Loading constraints...");
			int num = constraints.size();
			printNumber(num);
			constraints.add(c);
			int arity = c.scp.length;
			ctrArities.add(arity);
			ctrTypes.add(c.getClass().getSimpleName()
					+ (arity == 1 && !(c instanceof Extension1) ? "u" : (c instanceof Extension ? "-" + c.extStructure().getClass().getSimpleName() : "")));
			if (c.extStructure() instanceof Table)
				tableSizes.add(((Table) c.extStructure()).tuples.length);
			if (c instanceof CSmart)
				tableSizes.add(((TableSmart) c.extStructure()).smartTuples.length);
			return num;
		}

	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	private final Problem problem;

	/**
	 * The object used for collecting variables and constraints at construction (initialization)
	 */
	public Collecting collecting = new Collecting();

	protected final Repartitioner<Integer> varDegrees, domSizes, ctrArities, tableSizes;
	protected final Repartitioner<String> ctrTypes;

	public int nIsolatedVars, nFixedVars, nSymbolicVars;
	public int nRemovedUnaryCtrs, nConvertedConstraints; // conversion intension to extension
	public int nSpecificCtrs, nMergedCtrs, nDiscardedCtrs, nAddedCtrs;

	public long nEffectiveFilterings;

	public int nSharedBitVectors;

	/**
	 * Fields used when using reinforcing techniques (inferring AllDifferent constraints and symmetry-breaking constraints)
	 */
	public int nGenerators, nCliques;

	public ExternFunctionArity1 externFunctionArity1;
	public ExternFunctionArity2 externFunctionArity2;

	public int nValuesRemovedAtConstructionTime; // sum over all variable domains

	/**********************************************************************************************
	 * Methods for metrics
	 *********************************************************************************************/

	public int nDomTypes() {
		return (int) Stream.of(problem.variables).mapToInt(x -> x.dom.typeIdentifier()).distinct().count();
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

	protected Features(Problem problem) {
		this.problem = problem;
		boolean verbose = problem.head.control.general.verbose > 1;
		this.varDegrees = new Repartitioner<>(verbose);
		this.domSizes = new Repartitioner<>(verbose);
		this.ctrArities = new Repartitioner<>(verbose);
		this.ctrTypes = new Repartitioner<>(true);
		this.tableSizes = new Repartitioner<>(verbose);
	}

	public boolean hasSharedExtensionStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.extStructure() != null && c.extStructure().firstRegisteredCtr() != c);
	}

	public boolean hasSharedConflictsStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.conflictsStructure != null && c.conflictsStructure.firstRegisteredCtr() != c);
	}

	/**********************************************************************************************
	 * Methods for maps
	 *********************************************************************************************/

	public static class Attributes {

		public static final String SEPARATOR = "separator";

		private String name;

		private List<Entry<String, Object>> list = new ArrayList<>();

		public Attributes(String name) {
			this.name = name;
		}

		public Attributes put(String key, Object value, boolean condition) {
			if (value instanceof String && ((String) value).length() == 0)
				return this;
			if (value instanceof Integer && ((Integer) value) == 0 && !key.contentEquals("run"))
				return this;
			if (value instanceof Long && ((Long) value) == 0)
				return this;
			// if (value instanceof Number && ((Number) value).doubleValue() == 0)
			// return this;
			if (condition)
				list.add(new SimpleEntry<>(key, value));
			return this;
		}

		public Attributes put(String key, Object value) {
			return put(key, value, true);
		}

		public Attributes separator(boolean condition) {
			return put(SEPARATOR, null, condition);
		}

		public Attributes separator() {
			return put(SEPARATOR, null, true);
		}

		public List<Entry<String, Object>> entries() {
			return list.stream().filter(e -> e.getKey() != SEPARATOR).collect(Collectors.toCollection(ArrayList::new));
		}

		@Override
		public String toString() {
			String s = (name.equals(RUN) ? "" : Output.COMMENT_PREFIX + Kit.preprint(name, Kit.BLUE) + "\n") + Output.COMMENT_PREFIX + Output.COMMENT_PREFIX;
			boolean sep = true;
			for (int i = 0; i < list.size(); i++) {
				Entry<String, Object> e = list.get(i);
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

	public Attributes instanceAttributes(int instanceNumber) {
		SettingVars settings = problem.head.control.variables;
		Attributes m = new Attributes(INSTANCE);
		m.put(NAME, problem.name());
		m.put(NUMBER, instanceNumber, Input.nInstancesToSolve > 1);
		m.separator(settings.selectedVars.length > 0 || settings.instantiatedVars.length > 0 || settings.priorityVars.length > 0);
		m.put(SELECTION, Stream.of(settings.selectedVars).map(o -> o.toString()).collect(joining(",")));
		m.put(INSTANTIATION, IntStream.range(0, settings.instantiatedVars.length)
				.mapToObj(i -> settings.instantiatedVars[i] + "=" + settings.instantiatedVals[i]).collect(joining(",")));
		m.put(PRIORITY, Stream.of(settings.priorityVars).map(o -> o.toString()).collect(joining(",")));
		m.put(N_STRICT_PRIORITY, settings.nStrictPriorityVars);
		return m;
	}

	public Attributes domainsAttributes() {
		Attributes m = new Attributes(DOMAINS);
		m.put(N_TYPES, nDomTypes());
		m.put(N_VALUES, Variable.nValidValuesFor(problem.variables));
		Kit.control(nValuesRemovedAtConstructionTime == problem.nValueRemovals);
		m.put(N_DELETED, problem.nValueRemovals);
		m.put(SIZES, domSizes);
		return m;
	}

	public Attributes variablesAttributes() {
		Attributes m = new Attributes(VARIABLES);
		m.put(COUNT, problem.variables.length);
		m.put(N_DISCARDED, collecting.discardedVars.size());
		m.put(N_ISOLATED, nIsolatedVars);
		m.put(N_FIXED, nFixedVars);
		m.put(N_SYMBOLIC, nSymbolicVars);
		m.put(N_AUXILIARY, problem.nAuxVariables);
		m.put(DEGREES, varDegrees);
		return m;
	}

	public Attributes constraintsAttributes() {
		Attributes m = new Attributes(CONSTRAINTS);
		m.put(COUNT, problem.constraints.length);
		m.put(N_REMOVED1, nRemovedUnaryCtrs);
		m.put(N_CONVERTED, nConvertedConstraints);
		m.put(N_SPECIFIC, nSpecificCtrs);
		m.put(N_MERGED, nMergedCtrs);
		m.put(N_DISCARDED, nDiscardedCtrs);
		m.put(N_ADDED, nAddedCtrs);
		m.put(N_GENERATORS, nGenerators); // for symmetry-breaking constraints
		m.put(N_CLIQUES, nCliques); // for redundant AllDifferent constraints
		m.put(ARITIES, ctrArities);
		m.separator();
		m.put(DISTRIBUTION, ctrTypes);
		m.separator(tableSizes.repartition.size() > 0);
		m.put(TABLES, tableSizes.toString());
		m.put(N_TUPLES, tableSizes.repartition.entrySet().stream().mapToLong(e -> e.getValue() * (Integer) e.getKey()).sum());
		int nExtStructures = 0, nSharedExtStructures = 0, nIntStructures = 0, nSharedintStructures = 0, nCftStructures = 0, nSharedCftStructures = 0;
		for (Constraint c : problem.constraints) {
			if (c instanceof Extension)
				if (c.extStructure().firstRegisteredCtr() == c)
					nExtStructures++;
				else
					nSharedExtStructures++;
			if (c instanceof Intension)
				if (c.intStructure().firstRegisteredCtr() == c)
					nIntStructures++;
				else
					nSharedintStructures++;
			if (c.conflictsStructure != null)
				if (c.conflictsStructure.firstRegisteredCtr() == c)
					nCftStructures++;
				else
					nSharedCftStructures++;
		}
		m.separator(nExtStructures > 0 || nIntStructures > 0 || nCftStructures > 0 || nSharedBitVectors > 0);
		m.put(N_EXT_STRUCTURES, "(" + nExtStructures + ",shared:" + nSharedExtStructures + ")", nExtStructures > 0);
		m.put(N_INT_STRUCTURES, "(" + nIntStructures + ",shared:" + nSharedintStructures + ")", nIntStructures > 0);
		int unbuilt = problem.constraints.length - nCftStructures - nSharedCftStructures;
		m.put(N_CFT_STRUCTURES, "(" + nCftStructures + ",shared:" + nSharedCftStructures + ",unbuilt:" + unbuilt + ")", nCftStructures > 0);
		m.put(SHARED_BITS, nSharedBitVectors);
		m.separator();
		m.put(WCK, problem.head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, problem.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	public Attributes objectiveAttributes() {
		Kit.control(problem.optimizer.ctr != null);
		Attributes m = new Attributes(OBJECTIVE);
		m.put(WAY, (problem.optimizer.minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName());
		m.put(TYPE, problem.optimizer.ctr.getClass().getSimpleName());
		m.put(BOUNDS, (problem.optimizer.clb.limit() + ".." + problem.optimizer.cub.limit()));
		return m;
	}

}
