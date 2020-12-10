/**
 *  AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 *  All rights reserved. 
 *  
 *  This program and the accompanying materials are made 
 *  available under the terms of the CONTRAT DE LICENCE 
 *  DE LOGICIEL LIBRE CeCILL which accompanies this distribution, 
 *  and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;

public class TableWithSubtables extends Table {

	public int[][][][] subtables; // subtables[x][a][k] is the kth tuple of the table where x = a

	public int[] nextSupport(int x, int a, int[] current) {
		int[][] subtable = subtables[x][a];
		int res = Arrays.binarySearch(subtable, current, Utilities.lexComparatorInt);
		if (res >= 0)
			return current;
		int point = -res - 1;
		return point == subtable.length ? null : subtable[point];
	}

	protected void buildStructures() {
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
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		super.storeTuples(tuples, positive);
		buildStructures();
		assert IntStream.range(0, subtables.length).allMatch(i -> IntStream.range(0, subtables[i].length).allMatch(j -> Kit.isLexIncreasing(subtables[i][j])));
		// displayExhaustively();
	}

	public TableWithSubtables(Constraint c) {
		super(c);
	}

	@Override
	public String toString() {
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
