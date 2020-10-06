/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// from Gecode
public class Alpha implements ProblemAPI {

	private Var[] scope(Var[] x, String word) {
		return word.chars().mapToObj(i -> x[i - 'a']).toArray(Var[]::new);
	}

	@Override
	public void model() {
		Var[] x = array("x", size(26), dom(rangeClosed(1, 26)), "x[i] is the value for the ith letter of the alphabet");

		allDifferent(x);

		sum(scope(x, "ballet"), EQ, 45);
		sum(scope(x, "cello"), EQ, 43);
		sum(scope(x, "concert"), EQ, 74);
		sum(scope(x, "flute"), EQ, 30);
		sum(scope(x, "fugue"), EQ, 50);
		sum(scope(x, "glee"), EQ, 66);
		sum(scope(x, "jazz"), EQ, 58);
		sum(scope(x, "lyre"), EQ, 47);
		sum(scope(x, "oboe"), EQ, 53);
		sum(scope(x, "opera"), EQ, 65);
		sum(scope(x, "polka"), EQ, 59);
		sum(scope(x, "quartet"), EQ, 50);
		sum(scope(x, "saxophone"), EQ, 134);
		sum(scope(x, "scale"), EQ, 51);
		sum(scope(x, "solo"), EQ, 37);
		sum(scope(x, "song"), EQ, 61);
		sum(scope(x, "soprano"), EQ, 82);
		sum(scope(x, "theme"), EQ, 72);
		sum(scope(x, "violin"), EQ, 100);
		sum(scope(x, "waltz"), EQ, 34);
	}
}
