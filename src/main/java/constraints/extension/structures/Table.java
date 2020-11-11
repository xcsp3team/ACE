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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

import org.xcsp.common.Range;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

/**
 * This class is useful for table constraints, i.e., constraints defined in extension. All supports (allowed tuples) or all conflicts (disallowed
 * tuples) are recorded in a list. Note that tuples are recorded as indexes (of values).
 */
public class Table extends ExtensionStructure {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static int[][] shortTuplesForElement(Variable[] list, Variable index, int value) {
		Kit.control(Variable.areAllDistinct(list) && !Kit.isPresent(index, list));
		Kit.control(index.dom.areInitValuesExactly(new Range(list.length)) && Variable.areAllDomainsContainingValue(list, value));
		return IntStream.range(0, list.length).mapToObj(i -> IntStream.range(0, list.length + 1).map(j -> j == 0 ? i : j == i + 1 ? value : STAR).toArray())
				.toArray(int[][]::new);
	}

	public static int[][] shortTuplesForElement(Variable[] list, Variable index, Variable value) {
		Kit.control(Variable.areAllDistinct(list) && !Kit.isPresent(index, list) && index != value);
		Kit.control(index.dom.areInitValuesExactly(new Range(list.length)));
		Domain domResult = value.dom;
		int resultPositionInVector = Utilities.indexOf(value, list);
		int arity = resultPositionInVector == -1 ? list.length + 2 : list.length + 1;
		int resultPositionInTuple = resultPositionInVector == -1 ? arity - 1 : resultPositionInVector + 1;
		List<int[]> tuples = new ArrayList<>();
		for (int i = 0; i < list.length; i++) {
			Domain dom = list[i].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int v = dom.toVal(a);
				if (domResult.isPresentValue(v)) {
					int[] tuple = Kit.repeat(STAR, arity);
					tuple[0] = i;
					tuple[i + 1] = v;
					tuple[resultPositionInTuple] = v;
					tuples.add(tuple);
				}
			}
		}
		return Kit.intArray2D(tuples);
	}

	private static Map<String, int[][]> map = new HashMap<String, int[][]>();

	public static int[][] shortTuplesFordNotEqualVectors(Variable[] t1, Variable[] t2) {
		Kit.control(t1.length == t2.length);
		String key = "NotAllEqualVector " + Variable.signatureFor(t1) + " " + Variable.signatureFor(t2);
		int[][] tuples = map.get(key);
		if (tuples == null) {
			int k = t1.length;
			List<int[]> list = new ArrayList<int[]>();
			for (int i = 0; i < k; i++) {
				Domain dom1 = t1[i].dom, dom2 = t2[i].dom;
				for (int a = dom1.first(); a != -1; a = dom1.next(a)) {
					int v = dom1.toVal(a);
					for (int b = dom2.first(); b != -1; b = dom2.next(b)) {
						int w = dom2.toVal(b);
						if (v != w) {
							int[] tuple = Kit.repeat(STAR, 2 * k);
							tuple[i] = v;
							tuple[i + k] = w;
							list.add(tuple);
						}
					}
				}
			}
			tuples = Kit.intArray2D(list);
			map.put(key, tuples);
		}
		return tuples;
	}

	// public static Constraint buildlexicographicLt(Problem problem, Variable[] t1, Variable[] t2) {
	// Kit.control(t1.length == t2.length);
	// String key = "LexicographicLt " + Variable.getSignatureFor(t1) + " " + Variable.getSignatureFor(t2);
	// int[][] tuples = map.get(key);
	// if (tuples == null) {
	// int k = t1.length;
	// List<int[]> list = new ArrayList<int[]>();
	// for (int i = 0; i < k; i++) {
	// Domain dom0 = t1[0].dom
	//
	//
	// Domain dom1 = t1[i].dom, dom2 = t2[i].dom;
	// for (int idx1 = dom1.getFirstIdx(); idx1 != -1; idx1 = dom1.getNextIdx(idx1)) {
	// int val1 = dom1.toVal(idx1);
	// for (int idx2 = dom2.getFirstIdx(); idx2 != -1; idx2 = dom2.getNextIdx(idx2)) {
	// int val2 = dom2.toVal(idx2);
	// if (val1 != val2) {
	// int[] tuple = Kit.buildIntArrayWithUniqueValue(2 * k, Table.STAR_VALUE);
	// tuple[i] = val1;
	// tuple[i + k] = val2;
	// list.add(tuple);
	// }
	// }
	// }
	// }
	// tuples = Kit.toIntArray2D(list);
	// map.put(key, tuples);
	// }
	// ConstraintHardExtension ctr = new ConstraintHardExtensionJoker(problem, Variable.append(t1, t2));
	// // Kit.prn(Kit.implode2DStar(tuples));
	// ctr.key = key;
	// ctr.storeTuples(tuples, true);
	// return ctr;
	// }

	public static int[][] addStarInAtPosition(int[][] m, int position) {
		return IntStream.range(0, m.length)
				.mapToObj(i -> IntStream.range(0, m[0].length + 1).map(j -> j < position ? m[i][j] : j == position ? STAR : m[i][j - 1]).toArray())
				.toArray(int[][]::new);
	}

	/**********************************************************************************************
	 * Class
	 *********************************************************************************************/

	/**
	 * The set of supports or conflicts. The first array index corresponds to the order of the tuples. The second array index corresponds to the
	 * position of a value in a tuple.
	 */
	public int[][] tuples;

	public boolean positive;

	/**
	 * Indicates if the table is a short table (i.e., contains tuples with *)
	 */
	public boolean isShort;

	@Override
	public void storeTuples(int[][] m, boolean positive) {
		Constraint c = firstRegisteredCtr();
		this.isShort = false;
		if (m.length == 0)
			this.tuples = new int[0][]; // m;
		else {
			this.tuples = new int[m.length][c.scp.length];
			for (int j = 0; j < c.scp.length; j++) {
				Domain dom = c.scp[j].dom;
				for (int i = 0; i < m.length; i++) {
					int v = m[i][j];
					assert m[i].length == c.scp.length;
					assert v == STAR || dom.toIdx(v) != -1 : Kit.join(m[i]) + " j=" + j + " " + c + " " + dom;
					if (v == STAR)
						this.isShort = true;
					this.tuples[i][j] = v == STAR ? STAR : dom.toIdx(v);
				}
			}
		}
		this.positive = positive;
		Arrays.sort(this.tuples, Utilities.lexComparatorInt);
	}

	public Table(Constraint c) {
		super(c);
	}

	private boolean isMatching(int[] tuple, int[] idxs) {
		for (int i = 0; i < tuple.length; i++)
			if (tuple[i] != STAR && tuple[i] != idxs[i])
				return false;
		return true;
	}

	@Override
	public boolean checkIdxs(int[] t) {
		if (isShort) {
			for (int[] tuple : tuples)
				if (isMatching(tuple, t))
					return true;
			return false;
		}
		return (Arrays.binarySearch(tuples, t, Utilities.lexComparatorInt) >= 0) == positive;
	}

	@Override
	public String toString() {
		return "Tuples :\n" + Kit.join(tuples) + " (" + positive + ")";
	}

	@Override
	public int[] computeVariableSymmetryMatching() {
		return computeVariableSymmetryMatching(tuples, positive);
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
