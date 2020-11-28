/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import java.util.Arrays;
import java.util.stream.IntStream;

import constraints.extension.Extension.ExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.SubTable;
import constraints.extension.structures.Table;
import interfaces.Observers.ObserverSearch;
import interfaces.Tags.TagPositive;
import problem.Problem;
import sets.SetDense;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class ExtensionSTR3 extends ExtensionGlobal implements TagPositive, ObserverSearch {

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.tuples = ((Table) extStructure).tuples;
		this.set = new SetSparseReversible(tuples.length, pb.variables.length + 1);

		this.offsetsForMaps = new int[scp.length];
		for (int i = 1; i < offsetsForMaps.length; i++)
			offsetsForMaps[i] = offsetsForMaps[i - 1] + scp[i - 1].dom.initSize();
		int nValues = Variable.nInitValuesFor(scp);
		this.separatorsMaps = IntStream.rangeClosed(0, pb.variables.length).mapToObj(i -> new SetSparseMapSTR3(nValues, false))
				.toArray(SetSparseMapSTR3[]::new);
		// above do we need rangeClosed ?
		this.deps = IntStream.range(0, set.dense.length).mapToObj(i -> new LocalSetSparseByte(scp.length, false)).toArray(LocalSetSparseByte[]::new);
		if (set.capacity() >= Short.MAX_VALUE)
			separators = Variable.litterals(scp).intArray();
		else
			separatorsShort = Variable.litterals(scp).shortArray();

		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
		this.frontiers = new int[scp.length];
		this.subtables = ((SubTable) extStructure).subtables;
		this.subtablesShort = ((SubTable) extStructure).subtablesShort;
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
				separators[x][a] = map.separators[mapIndex];
			}
		} else {
			for (int i = map.limit; i >= 0; i--) {
				int mapIndex = dense[i];
				int x = map.positions[mapIndex];
				int a = mapIndex - offsetsForMaps[x];
				separatorsShort[x][a] = (short) map.separators[mapIndex];
			}
		}
		map.clear();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			frontiers[x] = doms[x].lastRemoved();
		}
	}

	public final class SetSparseMapSTR3 extends SetSparse {
		public short[] positions;

		public int[] separators;

		public SetSparseMapSTR3(int capacity, boolean initiallyFull) {
			super(capacity, initiallyFull);
			Kit.control(0 < capacity && capacity <= Short.MAX_VALUE);
			positions = Kit.range((short) capacity);
			separators = Kit.range(capacity);
		}

		@Override
		public final boolean add(int e) {
			throw new RuntimeException("Must not be called without a second argument");
		}

		public boolean add(int e, int position, int separator) {
			assert position < Byte.MAX_VALUE;
			boolean added = super.add(e);
			if (added) {
				positions[e] = (short) position;
				separators[e] = separator;
			}
			return added;
		}
	}

	// ************************************************************************
	// ***** Fields
	// ************************************************************************

	protected int[][] tuples;

	protected SetSparseReversible set;

	protected int[] frontiers; // 1D variable position

	/*** Fields related to propagation at preprocessing ***/

	protected boolean[][] ac; // ac[x][a] indicates if a support has been found for (x,a)

	protected int[] cnts; // cnts[x] is the number of values in the current domain of x with no found support (yet)

	/*** Fields related to propagation during search ***/

	protected int[][][] subtables; // 1D = variable (position) ; 2D = index ; 3D = order; value = position in sparseSetOfTuples

	protected int[][] separators; // 1D = variable (position) ; 2D = index ; value = separator in the associated subtable

	protected short[][][] subtablesShort; // 1D = variable (position) ; 2D = index ; 3D = order; value = position in sparseSetOfTuples

	protected short[][] separatorsShort; // 1D = variable (position) ; 2D = index ; value = separator in the associated subtable

	protected int[] offsetsForMaps; // 1D = variable (position)

	protected SetSparseMapSTR3[] separatorsMaps; // 1D = depth

	protected LocalSetSparseByte[] deps; // 1D = tuple position in sparseSetOfTuples ; value = variable position (so we can obtain the value in
	// the tuple)

	public ExtensionSTR3(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	final class LocalSetSparseByte {
		public byte[] dense;

		public byte[] sparse;

		public byte limit;

		public LocalSetSparseByte(int capacity, boolean initiallyFull) {
			Kit.control(0 < capacity && capacity <= Byte.MAX_VALUE);
			this.dense = Kit.range((byte) capacity);
			this.sparse = Kit.range((byte) capacity);
			this.limit = (byte) (initiallyFull ? dense.length - 1 : -1);
		}

		public boolean isPresent(byte e) {
			return sparse[e] <= limit;
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

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new SubTable(this);
	}

	// @Override
	// protected void initSpecificStructures() {
	//
	// }

	/**********************************************************************************************
	 * Methods related to propagation at preprocessing
	 *********************************************************************************************/

	protected int initializeBeforePropagationAtPreprocessing() {
		int cnt = 0;
		for (int i = 0; i < scp.length; i++) {
			cnt += (cnts[i] = doms[i].size());
			Arrays.fill(ac[i], false);
		}
		return cnt;
	}

	protected boolean updateDomainsAtPreprocessing(int cnt) {
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

	protected boolean filterAtPreprocessing() {
		int cnt = initializeBeforePropagationAtPreprocessing();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
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
		if (subtables != null) {
			for (int x = scp.length - 1; x >= 0; x--) {
				Domain dom = scp[x].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int[] subtable = subtables[x][a];
					int p = subtable.length - 1;
					while (!set.isPresent(subtable[p]))
						p--;
					separators[x][a] = p;
					p = 0;
					while (!set.isPresent(subtable[p]))
						p++;
					deps[subtable[p]].add((byte) x);
				}
			}
		} else {
			for (int x = scp.length - 1; x >= 0; x--) {
				Domain dom = scp[x].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					Kit.control(subtablesShort[x][a].length < Short.MAX_VALUE);
					short[] subtableShort = subtablesShort[x][a];
					int p = subtableShort.length - 1;
					while (!set.isPresent(subtableShort[p]))
						p--;
					separatorsShort[x][a] = (short) (p); // (subtablesShort[i][index].length - 1);
					p = 0;
					while (!set.isPresent(subtableShort[p]))
						p++;
					deps[subtableShort[p]].add((byte) x);
				}
			}
		}
	}

	/**********************************************************************************************
	 * Methods related to propagation during search
	 *********************************************************************************************/

	// bug to fix for java abscon.Resolution BinPacking-tab-Schwerin1_BPP10.xml.lzma -rc=10 -lc=4 -f=cop -positive=str3 -rn=20 -varh=DDegOnDom -ev
	protected void suppressInvalidTuplesFromRemovedValuesInDomainAtPosition(int x) {
		Domain dom = doms[x];
		if (subtables != null) {
			for (int a = dom.lastRemoved(); a != frontiers[x]; a = dom.prevRemoved(a)) {
				int[] t = subtables[x][a];
				for (int p = separators[x][a]; p >= 0; p--)
					set.removeIfPresent(t[p]);
			}
		} else {
			for (int a = dom.lastRemoved(); a != frontiers[x]; a = dom.prevRemoved(a)) {
				short[] t = subtablesShort[x][a];
				for (int p = separatorsShort[x][a]; p >= 0; p--)
					set.removeIfPresent(t[p]);
			}
		}
	}

	protected void supressInvalidTuples() {
		int limitBefore = set.limit;
		Variable lastPast = pb.solver.futVars.lastPast();
		if (lastPast != null && positionOf(lastPast) != -1)
			suppressInvalidTuplesFromRemovedValuesInDomainAtPosition(positionOf(lastPast));
		for (int i = futvars.limit; i >= 0; i--)
			suppressInvalidTuplesFromRemovedValuesInDomainAtPosition(futvars.dense[i]);
		if (set.limit < limitBefore) // tuples have been removed if this condition holds
			if (set.limits[pb.solver.depth()] == SetDense.UNINITIALIZED)
				set.limits[pb.solver.depth()] = limitBefore;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		pb.stuff.updateStatsForSTR(set);
		if (ac != null)
			return filterAtPreprocessing();
		SetSparseMapSTR3 map = separatorsMaps[pb.solver.depth()];
		int limitBefore = set.limit;
		supressInvalidTuples();
		if (subtables != null) {
			for (int i = set.limit + 1; i <= limitBefore; i++) {
				int[] tuple = tuples[set.dense[i]]; // suppressed tuple
				LocalSetSparseByte dependencies = deps[set.dense[i]];
				for (int j = dependencies.limit; j >= 0; j--) {
					byte x = dependencies.dense[j];
					if (!scp[x].assigned()) {
						int a = tuple[x];
						if (scp[x].dom.isPresent(a)) {
							int[] subtable = subtables[x][a];
							int separator = separators[x][a], p = separator;
							while (p >= 0 && !set.isPresent(subtable[p]))
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
				int[] supressedTuple = tuples[set.dense[i]];
				LocalSetSparseByte dependencies = deps[set.dense[i]];
				for (int j = dependencies.limit; j >= 0; j--) {
					byte x = dependencies.dense[j];
					if (!scp[x].assigned()) {
						int a = supressedTuple[x];
						if (scp[x].dom.isPresent(a)) {
							short[] subtable = subtablesShort[x][a];
							short separator = separatorsShort[x][a], p = separator;
							while (p >= 0 && !set.isPresent(subtable[p]))
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
