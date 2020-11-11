/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.List;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;

public class SubTable extends Table {

	public int[][][] subtables; // 1D = vap ; 2D = idx ; 3D = order; value = tid (position in tuples)

	public short[][][] subtablesShort;

	protected void buildSubtables() {
		Constraint ctr = firstRegisteredCtr();
		if (tuples.length >= Short.MAX_VALUE) {
			List<Integer>[][] tmp = Variable.litterals(ctr.scp).listArray();
			for (int i = 0; i < tuples.length; i++)
				for (int j = 0; j < tuples[i].length; j++)
					tmp[j][tuples[i][j]].add(i);
			subtables = Kit.intArray3D(tmp);
		} else {
			List<Short>[][] tmp = Variable.litterals(ctr.scp).listArray();
			for (int i = 0; i < tuples.length; i++)
				for (int j = 0; j < tuples[i].length; j++)
					tmp[j][tuples[i][j]].add((short) i);
			subtablesShort = Kit.shortArray3D(tmp);
		}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		super.storeTuples(tuples, positive);
		buildSubtables();
	}

	public SubTable(Constraint c) {
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
