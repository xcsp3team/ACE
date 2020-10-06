/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class TestArrays implements ProblemAPI {
	int n;

	String[] names;

	void data() {
		n = imp().askInt("Order (n)", "%03d");
		names = new String[] { "toto", "titi", "tata" };
	}

	@Override
	public void model() {
		Var yellow = var("yellow", dom(range(1, 6)));
		Var green = var("green", dom(range(1, 6)));
		Var red = var("red", dom(range(1, 6)));
		Var[] x = array("x", size(n), dom(range(n)), "x[i] is the ith value of the series");
		// Var[] y = array("y", size(n), dom(range(1, n - 1)), "y[i] is the distance between x[i] and x[i+1]");
		// Var[][] z = array("z", size(n, n), dom(range(n)));
		// VarSymbolic[] sb = arraySymbolic("sb", size(6), dom(names));

		block(() -> {
			equal(x[1], x[2]);
			lessThan(x[1], x[2]);
		}).tag(CLUES);
		forall(range(4), i -> {
			forall(range(3), j -> extension(vars(green, yellow), table("(1,2)")).note("yes.").tag(CLUES)).note("uuoooou");
			if (i % 2 == 1)
				equal(red, yellow).tag("toto");
			else
				extension(vars(red, yellow), table("(1,2)")).tag("titi");
		}).tag(SYMMETRY_BREAKING);
		block(() -> {
			block(() -> {
				Var pink = var("pink", dom(range(1, 6)));
				equal(pink, 3);
			}).tag("zertz");
		}).tag(CLUES);
		forall(range(4), i -> {
			block(() -> forall(range(3), j -> {
				extension(vars(green, yellow), table("(1,2)")).note("uuoooou");
				equal(x[1], x[2]);
			}).tag("zozo"));
			if (i % 2 == 1)
				equal(red, yellow).tag("toto");
			else
				extension(vars(red, yellow), table("(1,2)")).tag("titi");

		}).tag(SYMMETRY_BREAKING);

		// System.out.println(imp().ctrEntities);

	}

}
