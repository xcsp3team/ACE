/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.Arrays;
import java.util.Random;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.primitive.EQADD;
import problem.Problem;
import variables.Variable;

public class TestGauss implements ProblemAPI {
	int d;

	int[] holes(int k) {
		return IntStream.range(0, k * d).filter(i -> (i / d) % 2 == 0).toArray();
	}

	int[] rand(int[] t) {
		Random random = new Random(0);
		return Arrays.stream(t).filter(i -> random.nextDouble() < 0.2).toArray();
	}

	@Override
	public void model() {
		int[] t = range(1, d + 1).map(i -> i * i);

		Var x = var("x", dom(range(1, d + 2)));
		Var y = var("y", dom(t));
		Var z = var("z", dom(t));

		if (modelVariant("m1"))
			((Problem) imp()).addCtr(new EQADD(((Problem) imp()), (Variable) x, (Variable) y, (Variable) z));
		else if (modelVariant("m2"))
			equal(x, add(y, z));
		else
			sum(vars(y, z), EQ, x);
	}
}