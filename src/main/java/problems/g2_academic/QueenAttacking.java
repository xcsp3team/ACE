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

import utility.Kit;

/* "Prime queen attacking problem." + "\n See http://4c.ucc.ie/~tw/csplib/prob/prob029/index.html" */
public class QueenAttacking implements ProblemAPI {
	int n;

	@Override
	public void model() {
		int[] primes = Kit.computePrimes(n * n);
		int m = primes.length;

		Var q = var("q", dom(range(n * n)), "q is the cell for the queen");
		Var[] x = array("x", size(n * n), dom(range(n * n)), "x[i] is the cell for the i+1th value");
		// Var[] b = array("b", size(m), dom(0, 1), "b[i] is 0 if the ith prime value is not attacked");

		allDifferent(x).note("all values are put in different cells");
		slide(x, range(n * n - 1), i -> intension(knightAttack(x[i], x[i + 1], n))).note("ensuring a knight move between two successive values");
		// forall(range(m), i -> equal(b[i], not(queenAttack(q, x[primes[i] - 1], n)))).note("computing primes attacked by the queen");

		minimize(SUM, treesFrom(range(m), i -> not(queenAttack(q, x[primes[i] - 1], n)))).note("minimizing the number of free primes");

		// setpriorityVars(q);
	}

	@Override
	public void prettyDisplay(String[] values) {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++)
				for (int k = 1; k <= n * n; k++)
					if (Integer.parseInt(values[k]) == i * n + j) {
						System.out.print((k < 10 ? "0" + k : k) + " ");
						break;
					}
			System.out.println();
		}
	}

}
