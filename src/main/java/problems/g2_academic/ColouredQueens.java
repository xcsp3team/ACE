/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * The queens graph is a graph with n*n nodes corresponding to the squares of a chess-board. There is an edge between nodes iff they are on the same
 * row, column, or diagonal, i.e. if two queens on those squares would attack each other. The coloring problem is to color the queens graph with n
 * Colors. See Tom Kelsey, Steve Linton, Colva M. Roney-Dougal: New Developments in Symmetry Breaking in Search Using Computational Group Theory. AISC
 * 2004: 199-210.
 */
public class ColouredQueens implements ProblemAPI {

	int n;

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), dom(range(n)), "x[i][j] is the color at row i and column j");
		Var[][] dn = diagonalsDown(x), up = diagonalsUp(x); // pre-computing scopes of diagonals

		allDifferentMatrix(x).note("different colors on rows and columns");
		forall(range(dn.length), i -> allDifferent(dn[i]).note("different colors on downward diagonals"));
		forall(range(up.length), i -> allDifferent(up[i]).note("different colors on upward diagonals"));
	}
}
