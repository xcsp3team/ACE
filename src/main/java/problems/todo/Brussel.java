/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Brussel implements ProblemAPI {
	int[][] trains;

	@Override
	public void model() {
		int nTrains = trains.length;
		int max = IntStream.range(0, nTrains).map(i -> trains[i][0] + trains[i][1]).max().getAsInt();

		System.out.println("Max=" + max);
		Var[] x = array("x", size(nTrains), dom(range(max)), "x[i] is the starting time of the ith train");
		// Var[] c = array("c", size(nTrains), i -> dom(IntStream.range(0, max).map(j -> j * trains[i][2]).toArray()), "c[i] is the delay
		// cost of the ith train");

		noOverlap(x, IntStream.range(0, nTrains).map(i -> trains[i][1]).toArray());

		// forall(range(nTrains), i -> )
	}
}
