/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension.structures;

import static org.xcsp.common.Constants.STAR;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Range;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.ConstraintExtension;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This is the class for the tabular forms of extension structures. All supports (allowed tuples) or all conflicts
 * (disallowed tuples) are simply recorded in an array. Note that tuples are recorded with indexes (of values).
 * 
 * @author Christophe Lecoutre
 */
public class Table extends ExtensionStructure {

	/**********************************************************************************************
	 * Static Methods for Starred Tables
	 *********************************************************************************************/

	/**
	 * Cache used for some starred constructions of global constraints
	 */
	private static Map<String, int[][]> cache = new HashMap<>();

	/**
	 * Returns a starred table corresponding to the specified Element constraint
	 * 
	 * @param list
	 *            the parameter 'list' (vector) of the Element constraint
	 * @param index
	 *            the parameter 'index' of the Element constraint
	 * @param value
	 *            the parameter 'value' of the Element constraint
	 * @return a starred table corresponding to the specified Element constraint
	 */
	public static int[][] starredElement(Variable[] list, Variable index, int value) {
		control(Variable.areAllDistinct(list) && !index.presentIn(list));
		control(index.dom.areInitValuesExactly(new Range(list.length)) && Stream.of(list).allMatch(x -> x.dom.containsValue(value)));
		return IntStream.range(0, list.length).mapToObj(i -> IntStream.range(0, list.length + 1).map(j -> j == 0 ? i : j == i + 1 ? value : STAR).toArray())
				.toArray(int[][]::new);
	}

	/**
	 * Returns a starred table corresponding to the specified Element constraint
	 * 
	 * @param list
	 *            the parameter 'list' (vector) of the Element constraint
	 * @param index
	 *            the parameter 'index' of the Element constraint
	 * @param value
	 *            the parameter 'value' of the Element constraint
	 * @return a starred table corresponding to the specified Element constraint
	 */
	public static int[][] starredElement(Variable[] list, Variable index, Variable value) {
		control(Variable.areAllDistinct(list) && !index.presentIn(list) && index != value);
		control(index.dom.areInitValuesExactly(new Range(list.length)));
		Domain domResult = value.dom;
		int resultPositionInVector = Utilities.indexOf(value, list);
		int arity = resultPositionInVector == -1 ? list.length + 2 : list.length + 1;
		int resultPositionInTuple = resultPositionInVector == -1 ? arity - 1 : resultPositionInVector + 1;
		List<int[]> tuples = new ArrayList<>();
		for (int i = 0; i < list.length; i++) {
			Domain dom = list[i].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int v = dom.toVal(a);
				if (domResult.containsValue(v)) {
					int[] tuple = Kit.repeat(STAR, arity);
					tuple[0] = i;
					tuple[i + 1] = v;
					tuple[resultPositionInTuple] = v;
					tuples.add(tuple);
				}
			}
		}
		return tuples.stream().toArray(int[][]::new);
	}

	public static int[][] starredDistinctVectors(Variable[] t1, Variable[] t2) {
		control(t1.length == t2.length);
		String key = "DistinctVectors " + Variable.signatureFor(t1) + " " + Variable.signatureFor(t2);
		int[][] tuples = cache.get(key);
		if (tuples == null) {
			int half = t1.length;
			List<int[]> list = new ArrayList<>();
			for (int i = 0; i < half; i++) {
				Domain dom1 = t1[i].dom, dom2 = t2[i].dom;
				for (int a = dom1.first(); a != -1; a = dom1.next(a)) {
					int va = dom1.toVal(a);
					for (int b = dom2.first(); b != -1; b = dom2.next(b)) {
						int vb = dom2.toVal(b);
						if (va != vb) {
							int[] tuple = Kit.repeat(STAR, 2 * half);
							tuple[i] = va;
							tuple[i + half] = vb;
							list.add(tuple);
						}
					}
				}
			}
			tuples = list.stream().toArray(int[][]::new);
			cache.put(key, tuples);
		}
		return tuples;
	}

	public static int[][] starredLexicographicLt(Variable[] t1, Variable[] t2) {
		control(t1.length == t2.length);
		String key = "LexicographicLt " + Variable.signatureFor(t1) + " " + Variable.signatureFor(t2);
		int[][] tuples = cache.get(key);
		if (tuples == null) {
			int half = t1.length;
			List<int[]> list = new ArrayList<>();
			for (int i = 0; i < half; i++) {
				Domain dom1 = t1[i].dom, dom2 = t2[i].dom;
				for (int a = dom1.first(); a != -1; a = dom1.next(a)) {
					int va = dom1.toVal(a);
					for (int b = dom2.first(); b != -1; b = dom2.next(b)) {
						int vb = dom2.toVal(b);
						if (va < vb) {
							int[] tuple = Kit.repeat(STAR, 2 * half);
							tuple[i] = va;
							tuple[i + half] = vb;
							list.add(tuple);
						}
					}
				}
			}
			tuples = list.stream().toArray(int[][]::new);
			cache.put(key, tuples);
		}
		return tuples;
	}

	private static void addNonOverlappingTuplesFor(List<int[]> list, Domain dom1, Domain dom2, int offset, boolean first, boolean xAxis) {
		for (int a = dom1.first(); a != -1; a = dom1.next(a)) {
			int va = dom1.toVal(a);
			for (int b = dom2.last(); b != -1; b = dom2.prev(b)) {
				int vb = dom2.toVal(b);
				if (va + offset > vb)
					break;
				list.add(xAxis ? new int[] { first ? va : vb, first ? vb : va, STAR, STAR } : new int[] { STAR, STAR, first ? va : vb, first ? vb : va });
			}
		}
	}

	public static int[][] starredNoOverlap(Variable x1, Variable x2, Variable y1, Variable y2, int w1, int w2, int h1, int h2) {
		List<int[]> list = new ArrayList<>();
		addNonOverlappingTuplesFor(list, x1.dom, x2.dom, w1, true, true);
		addNonOverlappingTuplesFor(list, x2.dom, x1.dom, w2, false, true);
		addNonOverlappingTuplesFor(list, y1.dom, y2.dom, h1, true, false);
		addNonOverlappingTuplesFor(list, y2.dom, y1.dom, h2, false, false);
		return list.stream().toArray(int[][]::new);
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public boolean checkIndexes(int[] t) {
		if (starred) { // if starred, then necessarily positive table (for the moment)
			extern: for (int[] tuple : tuples) {
				for (int i = 0; i < tuple.length; i++)
					if (tuple[i] != STAR && tuple[i] != t[i])
						continue extern;
				return true;
			}
			return false;
		}
		return (Arrays.binarySearch(tuples, t, Utilities.lexComparatorInt) >= 0) == positive; // costly but not used
																								// during filtering
	}

	/**
	 * The set of supports or conflicts; tuples[k] is the kth tuple of the table
	 */
	public int[][] tuples;

	/**
	 * Indicates if tuples are supports or conflicts
	 */
	public boolean positive;

	/**
	 * Indicates if the table is a starred/short table (i.e., contains tuples with *)
	 */
	public boolean starred;

	/**
	 * Builds a table as extension structure for the specified extension constraint
	 * 
	 * @param c
	 *            a constraint
	 */
	public Table(ConstraintExtension c) {
		super(c);
	}

	@Override
	public void storeTuples(int[][] m, boolean positive) {
		this.starred = false;
		if (m.length == 0)
			this.tuples = new int[0][];
		else {
			Domain[] doms = firstRegisteredCtr().doms;
			this.tuples = new int[m.length][doms.length];
			for (int j = 0; j < doms.length; j++) {
				for (int i = 0; i < m.length; i++) {
					int v = m[i][j];
					assert m[i].length == doms.length;
					assert v == STAR || doms[j].toIdx(v) != -1 : Kit.join(m[i]) + " j=" + j + " " + firstRegisteredCtr() + " " + doms[j];
					if (v == STAR)
						this.starred = true;
					this.tuples[i][j] = v == STAR ? STAR : doms[j].toIdx(v);
				}
			}
		}
		this.positive = positive;
		Arrays.sort(this.tuples, Utilities.lexComparatorInt);
		control(!starred || positive);
		if (subtables != null)
			buildSubtables();
	}

	@Override
	public String toString() {
		return "Tuples :\n" + Kit.join(tuples) + " (" + positive + ")";
	}

	/**********************************************************************************************
	 * Handling subclasses (only for some algorithms like ExtensionVA (valid-allowed))
	 *********************************************************************************************/

	/**
	 * subtables[x][a][k] is the kth tuple of the table where x = a
	 */
	private int[][][][] subtables;

	public Table withSubtables() {
		this.subtables = new int[0][][][]; // to know that subtables must be created
		return this;
	}

	@Override
	public int[] nextSupport(int x, int a, int[] current) { // can only called by some algorithms (if subtables have
															// been created)
		int[][] subtable = subtables[x][a];
		int res = Arrays.binarySearch(subtable, current, Utilities.lexComparatorInt);
		if (res >= 0)
			return current;
		int point = -res - 1;
		return point == subtable.length ? null : subtable[point];
	}

	private void buildSubtables() {
		Constraint c = firstRegisteredCtr();
		List<int[]>[][] tmp = Variable.litterals(c.scp).listArray();
		for (int i = 0; i < tuples.length; i++)
			for (int j = 0; j < tuples[i].length; j++)
				tmp[j][tuples[i][j]].add(tuples[i]);
		subtables = new int[c.scp.length][][][];
		for (int i = 0; i < subtables.length; i++) {
			subtables[i] = new int[c.scp[i].dom.initSize()][][];
			for (int j = 0; j < subtables[i].length; j++)
				subtables[i][j] = tmp[i][j].toArray(new int[tmp[i][j].size()][]);
		}
		assert IntStream.range(0, subtables.length).allMatch(i -> IntStream.range(0, subtables[i].length).allMatch(j -> Kit.isLexIncreasing(subtables[i][j])));
	}

	String printSubtables() {
		StringBuilder sb = new StringBuilder(super.toString());
		sb.append("Subtables\n");
		for (int i = 0; i < subtables.length; i++) {
			sb.append("Variable " + firstRegisteredCtr().scp[i] + "\n");
			for (int j = 0; j < subtables[i].length; j++) {
				sb.append("  " + j + " :");
				for (int k = 0; k < subtables[i][j].length; k++)
					sb.append(" (" + Kit.join(subtables[i][j][k]) + ")");
				sb.append("\n");
			}
		}
		return sb.toString();
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
