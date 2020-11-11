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

import constraints.Constraint;

// See Lhomme and Régin 2005
public class TableWithNextIn extends Table {

	public int[][][] nextIn; // 1D = tuple position ; 2D = variable id ; 3D = index ; value = position of the next tuple

	protected void buildStructures() {
		Constraint c = firstRegisteredCtr();
		this.nextIn = new int[tuples.length][c.scp.length][];
		for (int i = 0; i < nextIn.length; i++) {
			for (int j = 0; j < nextIn[i].length; j++)
				nextIn[i][j] = new int[c.scp[j].dom.initSize()];
			int[] tuple = tuples[i];
			for (int j = 0; j < tuple.length; j++) {
				int a = tuple[j];
				for (int k = i - 1; k >= 0; k--)
					if (nextIn[k][j][a] == 0)
						nextIn[k][j][a] = i;
					else
						break;
			}
		}
		for (int j = 0; j < c.scp.length; j++)
			for (int a = 0; a < c.scp[j].dom.initSize(); a++) {
				for (int k = nextIn.length - 1; k >= 0; k--)
					if (nextIn[k][j][a] == 0)
						nextIn[k][j][a] = Integer.MAX_VALUE;
					else
						break;
			}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		super.storeTuples(tuples, positive);
		buildStructures();
	}

	public TableWithNextIn(Constraint c) {
		super(c);
	}

}
