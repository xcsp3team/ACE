/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import static org.xcsp.common.Constants.STAR;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import constraints.ConstraintExtension;
import constraints.extension.CSegmented;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import problem.Problem;
import sets.SetDenseReversible;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This class denote any constraint defined in extension. All supports (allowed tuples) or all conflicts (disallowed tuples) are recorded in a list. Note that
 * tuples are recorded as indexes (of values).
 */
public class TableSegmented extends ExtensionStructure {

	public static final class SegmentedTuple {

		/** The scope of the constraint on which the split tuple is defined. */
		private Variable[] scp;

		/** The tuple serving as basis for this split tuple. */
		private int[] prefixWithValues;

		/** The tuple serving as basis for this split tuple, with indices instead of values. */
		private int[] prefix;

		/** The set of restrictions associated with this split tuple. */
		public final RestrictionTable[] restrictions;

		/** unsupported[x] gives the sparse set of (value) indexes for which no support has been found yet. */
		private SetSparse[] unsupported;

		/**
		 * globalac[x] is a reference to the array ac managed by the restriction where x is involved (no overlap possible between restrictions) if x is not
		 * involved in any restriction, we have globalac[x] equal to null
		 */
		private boolean[][] globalac;

		public SegmentedTuple(int[] prefixWithValues, RestrictionTable[] restrictions) {
			this.prefixWithValues = prefixWithValues;
			this.restrictions = restrictions == null ? new RestrictionTable[0] : restrictions;
		}

		public void attach(CSegmented ctr) {
			this.scp = ctr.scp;
			this.prefixWithValues = prefixWithValues != null ? prefixWithValues : Kit.repeat(STAR, scp.length);
			this.prefix = IntStream.range(0, scp.length).map(i -> prefixWithValues[i] == STAR ? STAR : scp[i].dom.toIdx(prefixWithValues[i])).toArray();
			this.unsupported = ctr.unsupported;
			assert Variable.areSortedDomainsIn(scp);
			this.globalac = new boolean[ctr.scp.length][];
			for (RestrictionTable restriction : restrictions)
				for (int i = 0; i < restriction.subscp.length; i++) {
					restriction.positionsInScp = Stream.of(restriction.subscp).mapToInt(x -> Utilities.indexOf(x, scp)).toArray();
					restriction.positionsInSubscp = Stream.of(scp).mapToInt(x -> Utilities.indexOf(x, restriction.subscp)).toArray();
					globalac[restriction.positionsInScp[i]] = restriction.ac[i];
				}
		}

		/**
		 * Returns true iff the the split tuple "contains" the specified tuple
		 */
		public boolean contains(int[] tuple) {
			for (int i = 0; i < tuple.length; i++)
				if (prefix[i] != STAR && prefix[i] != tuple[i])
					return false;
			for (RestrictionTable restriction : restrictions)
				if (!restriction.contains(tuple))
					return false;
			return true;
		}

		/**
		 * Returns true iff the the segmented tuple is valid, considering the specified set of positions to check.
		 */
		public final boolean isValid(int[] sVal, int sValSize) {
			for (int i = sValSize - 1; i >= 0; i--) {
				int x = sVal[i];
				int a = prefix[x];
				if (a != STAR && !scp[x].dom.contains(a))
					return false;
			}
			for (RestrictionTable restriction : restrictions)
				if (restriction.isValid(sVal, sValSize) == false)
					return false;
			return true;
		}

		/**
		 * Collect supported indexes for the specified set of positions to consider.
		 */
		public final int collect(int[] sSup, int sSupSize) {
			for (RestrictionTable restriction : restrictions)
				restriction.collect(sSup, sSupSize);
			for (int i = sSupSize - 1; i >= 0; i--) {
				int x = sSup[i];
				assert unsupported[x].isEmpty() == false;
				if (globalac[x] == null) { // meaning that x is not involved in any subtable
					int a = prefix[x];
					if (a == STAR)
						unsupported[x].clear();
					else
						unsupported[x].remove(a);
				} else {
					for (int j = unsupported[x].limit; j >= 0; j--) {
						int a = unsupported[x].dense[j];
						if (globalac[x][a])
							unsupported[x].remove(a);
					}
				}
				if (unsupported[x].isEmpty())
					sSup[i] = sSup[--sSupSize];
			}
			return sSupSize;
		}

		@Override
		public String toString() {
			String s = "Split tuple : ";
			s += prefix == null ? "" : Kit.join(prefix, (Integer i) -> i == STAR ? "*" : i.toString());
			return s + " : " + Stream.of(restrictions).map(r -> r.toString()).collect(Collectors.joining(", "));
		}

		public static class RestrictionTable implements ObserverOnBacktracksSystematic {

			@Override
			public void restoreBefore(int depth) {
				set.restoreLimitAtLevel(depth);
			}

			private Problem pb;

			private Variable[] subscp;

			private Domain[] subdoms;

			protected int[][] subtable;

			private int[] positionsInScp;

			private int[] positionsInSubscp;

			public SetDenseReversible set;

			/**
			 * ac[x][a] indicates if a support has been found for (x,a)
			 */
			protected boolean[][] ac;

			/**
			 * cnts[x] is the number of values in the current domain of x with no found support (yet)
			 */
			protected int[] cnts;

			private int[] sLocal;
			private int sLocalSize;

			public void onConstructionProblemFinished(Problem pb) {
				this.pb = pb;
				this.set = new SetDenseReversible(subtable.length, pb.variables.length + 1);
			}

			public RestrictionTable(Variable[] subscp, int[][] subtable) {
				this.subscp = subscp;
				this.subdoms = Stream.of(subscp).map(x -> x.dom).toArray(Domain[]::new);
				this.subtable = subtable;
				this.ac = Variable.litterals(subscp).booleanArray();
				this.cnts = new int[subscp.length];
				Kit.control(subtable.length > 0);
				this.sLocal = new int[subscp.length];
			}

			private void fillLocal(int[] sGlobal, int sGlobalSize) {
				sLocalSize = 0;
				for (int i = sGlobalSize - 1; i >= 0; i--) {
					int x = sGlobal[i];
					int xlocal = positionsInSubscp[x];
					if (xlocal != -1)
						sLocal[sLocalSize++] = xlocal;
				}
			}

			private boolean isValid(int[] subtuple) {
				for (int i = sLocalSize - 1; i >= 0; i--) {
					int x = sLocal[i];
					int a = subtuple[x];
					if (a != STAR && !subdoms[x].contains(a))
						return false;
				}
				return true;
			}

			public boolean isValid(int[] sVal, int sValSize) {
				int depth = pb.solver.depth();
				fillLocal(sVal, sValSize);
				// TODO if sLocalSize = 0, we should be able to skip the traversal of the subtable. Right? idem for collecting ?
				for (int i = set.limit; i >= 0; i--) {
					int[] subtuple = subtable[set.dense[i]];
					if (isValid(subtuple) == false)
						set.removeAtPosition(i, depth);
				}
				return set.size() > 0;
			}

			private void collect(int[] sSup, int sSupSize) {
				// System.out.println("Collect for restriction " + Kit.join(subscp));
				fillLocal(sSup, sSupSize);
				for (int j = sLocalSize - 1; j >= 0; j--) {
					int x = sLocal[j];
					cnts[x] = subdoms[x].size();
					Arrays.fill(ac[x], false);
				}
				for (int i = set.limit; i >= 0; i--) {
					int[] subtuple = subtable[set.dense[i]];
					for (int j = sLocalSize - 1; j >= 0; j--) {
						int x = sLocal[j];
						if (cnts[x] > 0) {
							int a = subtuple[x];
							if (a == STAR) {
								cnts[x] = 0;
								Arrays.fill(ac[x], true);
								sLocal[j] = sLocal[--sLocalSize];
							} else if (!ac[x][a]) {
								ac[x][a] = true;
								if (--cnts[x] == 0)
									sLocal[j] = sLocal[--sLocalSize];
							}
						}
					}
				}
			}

			private boolean isMatching(int[] subtuple, int[] tuple) {
				for (int x = 0; x < subtuple.length; x++)
					if (subtuple[x] != STAR && subtuple[x] != tuple[positionsInScp[x]])
						return false;
				return true;
			}

			public boolean contains(int[] tuple) {
				for (int[] subtuple : subtable)
					if (isMatching(subtuple, tuple))
						return true;
				return false;
			}

			@Override
			public String toString() {
				return "\nsubscp=" + Utilities.join(subscp) + "\nsubtable=" + Utilities.join(subtable);
			}
		}
	}

	public final SegmentedTuple[] splitTuples;

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		throw new AssertionError();
	}

	public TableSegmented(ConstraintExtension c, SegmentedTuple[] splitTuples) {
		super(c);
		this.splitTuples = splitTuples;
	}

	@Override
	public boolean checkIndexes(int[] t) {
		for (SegmentedTuple splitTuple : splitTuples)
			if (splitTuple.contains(t))
				return true;
		return false;
	}

	@Override
	public String toString() {
		return "Split Tuples : " + Kit.join(splitTuples);
	}

}
