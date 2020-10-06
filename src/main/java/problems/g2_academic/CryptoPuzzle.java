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

/*
 * Crypto puzzle. Try this with DONALD + GERALD = ROBERT ; SUMMER + SCHOOL = COOLEST ; SEND + MORE = MONEY ; NO + NO = YES ; CROSS + ROADS = DANGER See
 * http://bach.istc.kobe-u.ac.jp/llp/crypt.html
 */
public class CryptoPuzzle implements ProblemAPI {
	String word1, word2, word3;

	@Override
	public void model() {
		int n = word1.length();
		control(word2.length() == n && (word3.length() == n || word3.length() == n + 1));
		int[] letters = singleValuesFrom((word1 + word2 + word3).chars(), i -> i - 'A');

		Var[] x = array("x", size(26), i -> dom(range(10)).when(contains(letters, i)),
				"x[i] is the value assigned to the ith letter (if present) of the alphabet");

		Var[] x1 = variablesFrom(new StringBuilder(word1).reverse().toString().chars(), i -> x[i - 'A']);
		Var[] x2 = variablesFrom(new StringBuilder(word2).reverse().toString().chars(), i -> x[i - 'A']);
		Var[] x3 = variablesFrom(new StringBuilder(word3).reverse().toString().chars(), i -> x[i - 'A']);

		if (modelVariant("carry")) {
			Var[] c = array("c", size(n + 1), dom(0, 1), "c[i] is the ith carry");

			allDifferent(x).note("all letters must be assigned different values");
			forall(range(3), i -> different(i == 0 ? x1[n - 1] : i == 1 ? x2[n - 1] : x3[x3.length - 1], 0))
					.note("the most significant letter of each word cannot be equal to 0");

			equal(c[0], 0).note("managing the least significant carry");
			equal(c[n], word3.length() == n ? 0 : x3[n]).note("managing the most significant carry");
			forall(range(n), i -> equal(mod(add(c[i], x1[i], x2[i]), 10), x3[i])).note("managing remainders");
			forall(range(n), i -> equal(div(add(c[i], x1[i], x2[i]), 10), c[i + 1])).note("managing quotients");
		} else {

			allDifferent(x).note("all letters must be assigned different values");
			// TODO

		}
	}
}
