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
package constraints.hard.extension.structures;

import constraints.Constraint;
import variables.Variable;

public class TableWithSubtablesExperimental1 extends TableWithSubtables {

	private int limit2 = 4, limit3 = 3;

	boolean[][][][] compatibles2;

	boolean[][][][][][] compatibles3;

	boolean[][][][] compatibles4;

	public boolean[][][][] getCompatibles2() {
		return compatibles2;
	}

	protected void buildStructures() {
		super.buildStructures();
		Constraint ctr = firstRegisteredCtr();
		Variable[] scope = ctr.scp;
		System.out.println("nb Variables " + scope.length);
		// if (!constraint.getIndexValueSimilarity()) {
		// //System.out.println("constraint = " + constraint);
		// throw new IllegalArgumentException();
		// }

		limit2 = ctr.scp.length - 1; // Math.min(limit2, constraint.getNbInvolvedVariables() - 3);
		compatibles2 = new boolean[limit2][ctr.scp.length][][];
		for (int i = 0; i < limit2; i++)
			for (int j = i + 1; j < scope.length; j++)
				compatibles2[i][j] = new boolean[scope[i].dom.initSize()][scope[j].dom.initSize()];

		for (int[] tuple : tuples) {
			for (int i = 0; i < limit2; i++) {
				boolean[][][] comps = compatibles2[i];
				int val = tuple[i];
				for (int j = i + 1; j < scope.length; j++)
					comps[j][val][tuple[j]] = true;
			}
		}

		limit3 = Math.min(limit3, ctr.scp.length - 3);
		compatibles3 = new boolean[limit2][limit2][ctr.scp.length][][][];
		for (int i = 0; i < limit2; i++)
			for (int j = i + 1; j < limit2; j++)
				for (int k = j + 1; k < scope.length; k++)
					compatibles3[i][j][k] = new boolean[scope[i].dom.initSize()][scope[j].dom.initSize()][scope[k].dom.initSize()];

		for (int[] tuple : tuples) {
			for (int i = 0; i < limit2; i++) {
				int val1 = tuple[i];
				for (int j = i + 1; j < limit2; j++) {
					boolean[][][][] nogoods = compatibles3[i][j];
					int val2 = tuple[j];
					for (int k = j + 1; k < scope.length; k++)
						nogoods[k][val1][val2][tuple[k]] = true;
				}
			}
		}

		// compatibles4 = new
		// boolean[variables[0].domain.getMaximumSize()][variables[1].domain.getMaximumSize()][variables[2].domain.getMaximumSize()][variables[3].domain
		// .getMaximumSize()];
		// for (int[] tuple : tuples)
		// compatibles4[tuple[0]][tuple[1]][tuple[3]][tuple[3]] = true;

		//
		for (int i = 0; i < limit2; i++)
			for (int j = i + 1; j < scope.length; j++)
				for (int k = 0; k < compatibles2[i][j].length; k++)
					for (int l = 0; l < compatibles2[i][j][k].length; l++)
						if (!compatibles2[i][j][k][l])
							System.out.println("nogood : " + i + " " + j + " : " + (char) (('a' + k)) + " " + (char) (('a' + l)));
	}

	public TableWithSubtablesExperimental1(Constraint ctr) {
		super(ctr);
	}

}
