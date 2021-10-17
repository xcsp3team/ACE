/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.ConstraintExtension;
import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Observers.ObserverOnSolving;
import interfaces.Tags.TagPositive;
import problem.Problem;
import sets.SetDense;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This is STR3 (Simple Tabular Reduction, v3), for filtering extension (table) constraints, as described in: <br />
 * "STR3: A path-optimal filtering algorithm for table constraints", Artificial Intelligence 220: 1-27 (2015) by C.
 * Lecoutre, C. Likitvivatanavong, and R. H. C. Yap.
 * 
 * @author Christophe Lecoutre
 */
public final class STR3 extends ExtensionSpecific implements TagPositive, ObserverOnSolving {

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		this.table = (TableAugmented) extStructure();
		this.set = new SetSparseReversible(table.tuples.length, n + 1);

		int nValues = Variable.nInitValuesFor(scp);
		this.separatorsMaps = IntStream.rangeClosed(0, n).mapToObj(i -> new SetSparseMapSTR3(nValues)).toArray(SetSparseMapSTR3[]::new);
		// above do we need rangeClosed ?
		this.deps = IntStream.range(0, set.dense.length).mapToObj(i -> new LocalSetSparseByte(scp.length, false)).toArray(LocalSetSparseByte[]::new);
		if (set.capacity() >= Short.MAX_VALUE)
			this.separators = Variable.litterals(scp).intArray();
		else
			this.separatorsShort = Variable.litterals(scp).shortArray();
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		SetSparseMapSTR3 map = separatorsMaps[depth];
		int[] dense = map.dense;
		if (separators != null) {
			for (int i = map.limit; i >= 0; i--) {
				int mapIndex = dense[i];
				int x = map.positions[mapIndex];
				int a = mapIndex - offsetsForMaps[x];
				separators[x][a] = map.sseparators[mapIndex];
			}
		} else {
			for (int i = map.limit; i >= 0; i--) {
				int mapIndex = dense[i];
				int x = map.positions[mapIndex];
				int a = mapIndex - offsetsForMaps[x];
				separatorsShort[x][a] = (short) map.sseparators[mapIndex];
			}
		}
		map.clear();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			frontiers[x] = doms[x].lastRemoved();
		}
	}

	/**********************************************************************************************
	 * Inner classes
	 *********************************************************************************************/

	private static final class TableAugmented extends Table {

		/**
		 * subtables[x][a][k] is the tid (position in tuples) of the kth tuple where x = a
		 */
		public int[][][] subtables;

		public short[][][] subtablesShort; // short version

		protected void buildSubtables() {
			Variable[] scp = firstRegisteredCtr().scp;
			if (tuples.length >= Short.MAX_VALUE) {
				List<Integer>[][] tmp = Variable.litterals(scp).listArray();
				for (int tid = 0; tid < tuples.length; tid++)
					for (int x = 0; x < scp.length; x++)
						tmp[x][tuples[tid][x]].add(tid);
				subtables = Stream.of(tmp).map(m -> Kit.intArray2D(m)).toArray(int[][][]::new);
			} else {
				List<Short>[][] tmp = Variable.litterals(scp).listArray();
				for (int tid = 0; tid < tuples.length; tid++)
					for (int x = 0; x < scp.length; x++)
						tmp[x][tuples[tid][x]].add((short) tid);
				subtablesShort = Stream.of(tmp).map(m -> Kit.shortArray2D(m)).toArray(short[][][]::new);
			}
		}

		@Override
		public void storeTuples(int[][] tuples, boolean positive) {
			super.storeTuples(tuples, positive);
			buildSubtables();
		}

		public TableAugmented(ConstraintExtension c) {
			super(c);
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			if (subtables != null)
				for (int i = 0; i < subtables.length; i++) {
					sb.append("Variable " + firstRegisteredCtr().scp[i] + "\n");
					for (int j = 0; j < subtables[i].length; j++)
						sb.append("  " + j + " : " + Kit.join(subtables[i][j]) + "\n");
				}
			if (subtablesShort != null)
				for (int i = 0; i < subtablesShort.length; i++) {
					sb.append("Variable " + firstRegisteredCtr().scp[i] + "\n");
					for (int j = 0; j < subtablesShort[i].length; j++)
						sb.append("  " + j + " : " + Kit.join(subtablesShort[i][j]) + "\n");
				}
			return sb.toString();
		}

	}

	private final class SetSparseMapSTR3 extends SetSparse {
		public short[] positions;

		public int[] sseparators;

		public SetSparseMapSTR3(int capacity) {
			super(capacity, false);
			control(0 < capacity && capacity <= Short.MAX_VALUE);
			this.positions = new short[capacity];
			for (short i = 0; i < positions.length; i++)
				positions[i] = i;
			this.sseparators = new int[capacity];
		}

		@Override
		public final boolean add(int a) {
			throw new RuntimeException("Must not be called without a second argument");
		}

		public boolean add(int a, int position, int separator) {
			assert position < Byte.MAX_VALUE;
			boolean added = super.add(a);
			if (added) {
				positions[a] = (short) position;
				sseparators[a] = separator;
			}
			return added;
		}
	}

	private final class LocalSetSparseByte {
		private byte[] dense;

		private byte[] sparse;

		private byte limit;

		public LocalSetSparseByte(int capacity, boolean initiallyFull) {
			control(0 < capacity && capacity <= Byte.MAX_VALUE);
			this.dense = new byte[capacity];
			for (byte i = 0; i < dense.length; i++)
				dense[i] = i;
			this.sparse = new byte[capacity];
			for (byte i = 0; i < sparse.length; i++)
				sparse[i] = i;
			this.limit = (byte) (initiallyFull ? dense.length - 1 : -1);
		}

		public boolean add(byte e) {
			byte i = sparse[e];
			if (i <= limit)
				return false; // not added because already present
			limit++;
			if (i > limit) {
				byte f = dense[limit];
				dense[i] = f;
				dense[limit] = e;
				sparse[e] = limit;
				sparse[f] = i;
			}
			return true; // added
		}

		public boolean remove(byte e) {
			byte i = sparse[e];
			if (i > limit)
				return false; // not removed because not present
			if (i != limit) {
				byte f = dense[limit];
				dense[i] = f;
				dense[limit] = e;
				sparse[e] = limit;
				sparse[f] = i;
			}
			limit--;
			return true; // removed
		}
	}

	/**********************************************************************************************
	 * Fields, constructor and preprocessing
	 *********************************************************************************************/

	/**
	 * The (augmented) table used with STR3
	 */
	private TableAugmented table;

	/**
	 * The reversible sparse set storing the indexes (of tuples) of the current table
	 */
	private SetSparseReversible set;

	/**
	 * Only used at preprocessing, ac[x][a] indicates if a support has been found for (x,a)
	 */
	private boolean[][] ac;

	/**
	 * Only used at preprocessing, cnts[x] is the number of values in the current domain of x with no found support
	 * (yet)
	 */
	private int[] cnts;

	/**
	 * separators[x][a] is the separator for (x,a) in the associated subtable
	 */
	private int[][] separators;

	private short[][] separatorsShort; // short version

	private final int[] offsetsForMaps; // 1D = variable (position)

	private SetSparseMapSTR3[] separatorsMaps; // 1D = depth

	/**
	 * deps[p] is the variable position of the tuple at position p in set (so we can obtain the value in the tuple)
	 */
	private LocalSetSparseByte[] deps;

	/**
	 * frontiers[x] is the frontier for variable x
	 */
	private final int[] frontiers;

	public STR3(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.offsetsForMaps = new int[scp.length];
		for (int i = 1; i < offsetsForMaps.length; i++)
			offsetsForMaps[i] = offsetsForMaps[i - 1] + scp[i - 1].dom.initSize();
		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
		this.frontiers = new int[scp.length];
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new TableAugmented(this);
	}

	/**********************************************************************************************
	 * Methods related to propagation at preprocessing
	 *********************************************************************************************/

	private boolean updateDomainsAtPreprocessing(int cnt) {
		for (int x = scp.length - 1; x >= 0 && cnt > 0; x--) {
			int nRemovals = cnts[x];
			if (nRemovals == 0)
				continue;
			if (scp[x].dom.remove(ac[x], nRemovals) == false)
				return false;
			cnt -= nRemovals;
		}
		return true;
	}

	private boolean filterAtPreprocessing() {
		int cnt = 0;
		for (int i = 0; i < scp.length; i++) {
			cnt += (cnts[i] = doms[i].size());
			Arrays.fill(ac[i], false);
		}
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = table.tuples[set.dense[i]];
			if (isValid(tuple)) {
				for (int x = scp.length - 1; x >= 0; x--) {
					int a = tuple[x];
					if (!ac[x][a]) {
						cnt--;
						cnts[x]--;
						ac[x][a] = true;
					}
				}
			} else
				set.removeAtPosition(i, 0);
		}
		return updateDomainsAtPreprocessing(cnt);
	}

	/**********************************************************************************************
	 * Methods called between preprocessing and search
	 *********************************************************************************************/

	@Override
	public void beforeSearch() {
		ac = null;
		cnts = null;
		for (int i = 0; i < frontiers.length; i++)
			frontiers[i] = doms[i].lastRemoved();
		// initialization of separators and deps
		if (table.subtables != null) {
			for (int x = scp.length - 1; x >= 0; x--) {
				for (int a = scp[x].dom.first(); a != -1; a = scp[x].dom.next(a)) {
					int[] subtable = table.subtables[x][a];
					int p = subtable.length - 1;
					while (!set.contains(subtable[p]))
						p--;
					separators[x][a] = p;
					p = 0;
					while (!set.contains(subtable[p]))
						p++;
					deps[subtable[p]].add((byte) x);
				}
			}
		} else {
			for (int x = scp.length - 1; x >= 0; x--) {
				for (int a = scp[x].dom.first(); a != -1; a = scp[x].dom.next(a)) {
					control(table.subtablesShort[x][a].length < Short.MAX_VALUE);
					short[] subtableShort = table.subtablesShort[x][a];
					int p = subtableShort.length - 1;
					while (!set.contains(subtableShort[p]))
						p--;
					separatorsShort[x][a] = (short) (p); // (subtablesShort[i][index].length - 1);
					p = 0;
					while (!set.contains(subtableShort[p]))
						p++;
					deps[subtableShort[p]].add((byte) x);
				}
			}
		}
	}

	/**********************************************************************************************
	 * Methods related to propagation during search
	 *********************************************************************************************/

	// bug to fix for java ace BinPacking-tab-Schwerin1_BPP10.xml.lzma -r_c=10 -lc=4 -positive=str3 -r_n=20
	// -varh=DDegOnDom -ev
	private void suppressInvalidTuplesFromRemovalsOf(int x) {
		Domain dom = doms[x];
		if (table.subtables != null) {
			for (int a = dom.lastRemoved(); a != frontiers[x]; a = dom.prevRemoved(a)) {
				int[] t = table.subtables[x][a];
				for (int p = separators[x][a]; p >= 0; p--)
					set.remove(t[p]);
			}
		} else {
			for (int a = dom.lastRemoved(); a != frontiers[x]; a = dom.prevRemoved(a)) {
				short[] t = table.subtablesShort[x][a];
				for (int p = separatorsShort[x][a]; p >= 0; p--)
					set.remove(t[p]);
			}
		}
	}

	private void supressInvalidTuples() {
		int limitBefore = set.limit;
		Variable lastPast = problem.solver.futVars.lastPast();
		if (lastPast != null && positionOf(lastPast) != -1)
			suppressInvalidTuplesFromRemovalsOf(positionOf(lastPast));
		for (int i = futvars.limit; i >= 0; i--)
			suppressInvalidTuplesFromRemovalsOf(futvars.dense[i]);
		if (set.limit < limitBefore) // tuples have been removed if this condition holds
			if (set.limits[problem.solver.depth()] == SetDense.UNINITIALIZED)
				set.limits[problem.solver.depth()] = limitBefore;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		if (ac != null)
			return filterAtPreprocessing();
		SetSparseMapSTR3 map = separatorsMaps[problem.solver.depth()];
		int limitBefore = set.limit;
		supressInvalidTuples();
		if (table.subtables != null) {
			for (int i = set.limit + 1; i <= limitBefore; i++) {
				int[] tuple = table.tuples[set.dense[i]]; // suppressed tuple
				LocalSetSparseByte dependencies = deps[set.dense[i]];
				for (int j = dependencies.limit; j >= 0; j--) {
					byte x = dependencies.dense[j];
					if (!scp[x].assigned()) {
						int a = tuple[x];
						if (scp[x].dom.contains(a)) {
							int[] subtable = table.subtables[x][a];
							int separator = separators[x][a], p = separator;
							while (p >= 0 && !set.contains(subtable[p]))
								p--;
							if (p < 0) {
								if (scp[x].dom.remove(a) == false)
									return false;
							} else {
								if (p != separator) {
									map.add(offsetsForMaps[x] + a, x, separator);
									separators[x][a] = p;
								}
								dependencies.remove(x);
								deps[subtable[p]].add(x);
							}
						}
					}
					// else dependencies.removePresentIndex(pos);
				}
			}
		} else {
			for (int i = set.limit + 1; i <= limitBefore; i++) {
				int[] supressedTuple = table.tuples[set.dense[i]];
				LocalSetSparseByte dependencies = deps[set.dense[i]];
				for (int j = dependencies.limit; j >= 0; j--) {
					byte x = dependencies.dense[j];
					if (!scp[x].assigned()) {
						int a = supressedTuple[x];
						if (scp[x].dom.contains(a)) {
							short[] subtable = table.subtablesShort[x][a];
							short separator = separatorsShort[x][a], p = separator;
							while (p >= 0 && !set.contains(subtable[p]))
								p--;
							if (p < 0) {
								if (!scp[x].dom.remove(a))
									return false;
							} else {
								if (p != separator) {
									map.add(offsetsForMaps[x] + a, x, separator);
									separatorsShort[x][a] = p;
								}
								dependencies.remove(x);
								deps[subtable[p]].add(x);
							}
						}
					}
					// else dependencies.removePresentIndex(pos);
				}
			}
		}
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			frontiers[x] = doms[x].lastRemoved();
		}
		return true;
	}

}
