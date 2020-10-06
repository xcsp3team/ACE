/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.tran;

import java.util.Scanner;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

// data from Kostas
public class RenaultMod implements ProblemAPI {
	int nVars, nCtrs;
	int[] nVals;
	int[][] scopes;
	int[][][] tuples;

	void data() {
		Scanner scanner = imp().fileScanner();
		scanner.nextInt();
		nVars = scanner.nextInt();
		nCtrs = scanner.nextInt();
		nVals = IntStream.range(0, nVars).filter(i -> i == scanner.nextInt()).map(i -> scanner.nextInt()).toArray();
		scopes = new int[nCtrs][];
		tuples = new int[nCtrs][][];
		for (int i = 0; i < nCtrs; i++) {
			Kit.control(scanner.nextInt() == i);
			int arity = scanner.nextInt(), nTuples = scanner.nextInt();
			scopes[i] = IntStream.range(0, arity).map(j -> scanner.nextInt()).toArray();
			tuples[i] = IntStream.range(0, nTuples).mapToObj(j -> IntStream.range(0, arity).map(k -> scanner.nextInt()).toArray()).toArray(int[][]::new);
		}
		scanner.close();
	}

	@Override
	public void model() {
		Var[] x = array("x", size(nVars), i -> dom(range(42))); // 42 to control
		forall(range(nVars), i -> intension(le(x[i], nVals[i] - 1)));
		forall(range(nCtrs), i -> extension(select(x, scopes[i]), tuples[i]));
	}
}
