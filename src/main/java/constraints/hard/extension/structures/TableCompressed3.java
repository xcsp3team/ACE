/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import java.util.Arrays;
import java.util.TreeSet;

import org.xcsp.common.Utilities;

import constraints.Constraint;
import utility.Kit;
import utility.Kit.IntArrayWithScore;
import variables.Variable;
import variables.domains.Domain;

/**
 * This class denote any constraint defined in extension. All supports (allowed tuples) or all conflicts (disallowed tuples) are recorded in
 * a list. Note that tuples are recorded as indexes (of values).
 */
public final class TableCompressed3 extends Table {

	private static final int MINIMAL_PATTERN_SIZE = 3;

	// private static final int MINIMAL_PATTERN_SCORE = 5;

	private int scoreThreshold = 50, nPatterns = 500;

	public int[][] patterns; // 1D = pattern id , 2D = pattern

	private int[] tmp;

	public static int compression;

	class Node {

		private Node[] childs;

		protected Node() {
		}

		Node(int nbChilds) {
			childs = new Node[nbChilds];
		}

		protected void add(int tupleId, int[] tuple, int position, int limit, int size) {
			// Kit.prn(position + " " + limit );
			if (childs[tuple[position]] == null)
				childs[tuple[position]] = position == limit - 1 ? new Leaf(tuple.length) : new Node(childs.length);
			childs[tuple[position]].add(tupleId, tuple, position + 1, limit, size);
		}

		protected void collectPatterns(TreeSet<IntArrayWithScore> patternsTree, int[] collect, int position) {
			for (int i = 0; i < childs.length; i++)
				if (childs[i] != null) {
					collect[position] = i;
					childs[i].collectPatterns(patternsTree, collect, position + 1);
				}
		}
	}

	class Leaf extends Node {
		private int lastTupleId = -1, lastPosition = -1;

		private int[] ranks;

		protected Leaf(int length) {
			ranks = new int[length];
		}

		protected void add(int tupleId, int[] tuple, int position, int limit, int size) {
			assert position == limit;
			if (tupleId != lastTupleId) {
				lastTupleId = tupleId;
				lastPosition = position - size;
				ranks[lastPosition]++;
			} else if (lastPosition + size - 1 < position - size) {
				lastPosition = position - size;
				ranks[lastPosition]++;
			}
		}

		private int computeScoreFromRanks() {
			int sum = 0;
			for (int val : ranks)
				sum += Math.max(0, val - 1);
			return sum;
		}

		protected void collectPatterns(TreeSet<IntArrayWithScore> patternsTree, int[] collect, int dummy) {
			int score = collect.length * computeScoreFromRanks();
			if (score >= scoreThreshold) {
				// Kit.prn("tree size " + tree.size());
				if (patternsTree.size() < nPatterns) {
					// boolean b =
					patternsTree.add(new IntArrayWithScore(collect.clone(), score));
					// Kit.prn("add " + b);
				} else {
					IntArrayWithScore o = patternsTree.first();
					// Kit.prn("first " + o.score);
					if (score > o.score) {
						patternsTree.pollFirst();
						patternsTree.add(new IntArrayWithScore(collect.clone(), score));
					}
				}
				// Kit.prn(Kit.implode(collect, pos) + " => score=" + score + " ranks=" + Kit.implode(ranks, ","));
			}
			// if (nb2 > 5)Kit.prn(Kit.implode(collect, pos) + " nb2=" + nb2 + " score=" + computeScoreFromRanks() + " ranks=" +
			// Kit.implode(ranks, ","));
		}
	}

	private TreeSet<IntArrayWithScore> buildPatterns(int[][] tuples, int nbDifferentValues) {
		// Kit.prn(this + " nbTuples=" + tuples.length);
		Node[] roots = new Node[tuples[0].length];
		int minSize = MINIMAL_PATTERN_SIZE, maxSize = roots.length - 1; // -1 because only one pattern possible of size scope.length
		for (int i = minSize; i <= maxSize; i++)
			roots[i] = new Node(nbDifferentValues);
		for (int i = 0; i < tuples.length; i++)
			for (int size = minSize; size <= maxSize; size++)
				for (int position = 0; position <= tuples[i].length - size; position++)
					roots[size].add(i, tuples[i], position, position + size, size);
		// int[] collect = new int[scope.length];
		TreeSet<IntArrayWithScore> patternsTree = new TreeSet<>();
		for (int i = minSize; i <= maxSize; i++)
			roots[i].collectPatterns(patternsTree, new int[i], 0);
		// Kit.prn("selection");
		// for (IntArrayWithScore o : patternsTree)
		// Kit.prn(Kit.implode(o.t) + " => " + o.score);
		return patternsTree;
	}

	private int search(int[] tuple, int position) {
		for (int i = 1; i < patterns.length; i++)
			if (Kit.isSubtuple(patterns[i], tuple, position))
				return i;
		return -1;
	}

	public void compressTableFrom(TreeSet<IntArrayWithScore> patternsTree) {
		patterns = new int[patternsTree.size() + 1][];
		int cnt = 1; // because 0 is both positive and negative
		for (IntArrayWithScore o : patternsTree)
			patterns[cnt++] = o.t;
		int[] tmp = new int[tuples[0].length];
		for (int i = 0; i < tuples.length; i++) {
			int length = 0;
			for (int position = 0; position < tuples[i].length;) {
				int patternIndex = search(tuples[i], position);
				if (patternIndex != -1) {
					tmp[length++] = -patternIndex;
					position += patterns[patternIndex].length;
				} else
					tmp[length++] = tuples[i][position++];
			}
			if (length != tuples[i].length) {
				compression += (tuples[i].length - length);
				// Kit.prn("reduc");
				assert controlCompression(tuples[i], tmp, length);
				tuples[i] = new int[length];
				System.arraycopy(tmp, 0, tuples[i], 0, length);
			}
		}
	}

	private boolean controlCompression(int[] tuple, int[] tmp, int length) {
		int[] compressedTuple = new int[length];
		System.arraycopy(tmp, 0, compressedTuple, 0, length);
		return Utilities.lexComparatorInt.compare(decompress(compressedTuple), tuple) == 0;
	}

	/**
	 * Records the list of supports or conflicts.
	 * 
	 * @param tuples
	 *            the list of tuples
	 * @param positive
	 *            indicates if the tuples correspond to supports (allowed tuples) or conflicts (disallowed tuples).
	 */
	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		Constraint ctr = firstRegisteredCtr();
		if (tuples.length == 0)
			this.tuples = tuples;
		else if (ctr.indexesMatchValues) {
			this.tuples = Kit.cloneDeeply(tuples);
		} else {
			this.tuples = new int[tuples.length][tuples[0].length];
			for (int j = 0; j < tuples[0].length; j++) {
				Domain dom = ctr.scp[j].dom;
				for (int i = 0; i < tuples.length; i++)
					this.tuples[i][j] = dom.toIdx(tuples[i][j]);
			}
		}
		this.positive = positive;
		tmp = new int[ctr.scp.length];
		Arrays.sort(this.tuples, Utilities.lexComparatorInt);
		TreeSet<IntArrayWithScore> patternsTree = buildPatterns(tuples, Variable.maxInitDomSize(firstRegisteredCtr().scp));
		compressTableFrom(patternsTree);
	}

	public TableCompressed3(Constraint ctr) {
		super(ctr);
	}

	public int[] decompress(int[] tuple) {
		for (int pos = 0, gap = 0; pos < tuple.length; pos++) {
			int val = tuple[pos];
			if (val >= 0)
				tmp[gap + pos] = val;
			else {
				int[] pattern = patterns[-val];
				// Kit.prn(" patt " + Kit.implode(pattern));
				for (int i = pattern.length - 1; i >= 0; i--)
					tmp[gap + pos + i] = pattern[i];
				gap += pattern.length - 1;
			}
		}
		return tmp;
	}

	@Override
	public boolean checkIdxs(int[] t) {
		int min = 0, max = tuples.length - 1;
		while (min <= max) {
			int med = (min + max) / 2;
			int res = Utilities.lexComparatorInt.compare(t, decompress(tuples[med]));
			if (res == 0)
				return true;
			if (res < 0)
				max = med - 1;
			if (res > 0)
				min = med + 1;
		}
		return false;
		// return true; //(Arrays.binarySearch(tuples, indexes, Kit.lexicographicComparator) >= 0) == positive;
	}

	@Override
	public String toString() {
		return "Tuples : " + Kit.join(tuples);
	}

}

// public void mergeWith(ExtensionStructure matrix, int[] mapping) {
// assert matrix instanceof Tuples;
// Tuples otherTuples = (Tuples) matrix;
//
// int[] dst = new int[mapping.length];
//
// int[] reverseMapping = new int[mapping.length];
// for (int i = 0; i < mapping.length; i++)
// reverseMapping[mapping[i]] = i;
//
// Set<int[]> set = new TreeSet<int[]>(comparator);
//
// if (supportOriented && otherTuples.supportOriented) {
// for (int i = 0; i < tuples.length; i++)
// if (Arrays.binarySearch(otherTuples.tuples, mapTuple(tuples[i], dst, mapping), comparator) >= 0)
// set.add(tuples[i]);
// } else if (!supportOriented && !otherTuples.supportOriented) {
// for (int i = 0; i < tuples.length; i++)
// set.add(tuples[i]);
// for (int i = 0; i < otherTuples.tuples.length; i++)
// set.add(mapTuple(otherTuples.tuples[i], dst, mapping).clone());
// } else if (supportOriented && !otherTuples.supportOriented) {
// for (int i = 0; i < tuples.length; i++)
// if (Arrays.binarySearch(otherTuples.tuples, mapTuple(tuples[i], dst, mapping), comparator) < 0)
// set.add(tuples[i]);
// } else if (!supportOriented && otherTuples.supportOriented) {
// for (int i = 0; i < otherTuples.tuples.length; i++)
// if (Arrays.binarySearch(tuples, mapTuple(otherTuples.tuples[i], dst, reverseMapping), comparator) < 0)
// set.add(otherTuples.tuples[i]);
// supportOriented = true;
// }
// tuples = set.toArray(new int[set.size()][]);
// }
