/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.extension.CtrExtensionSmart;
import constraints.hard.extension.structures.SmartTuple;
import problem.Problem;
import variables.Variable;

public class TestSmart implements ProblemAPI {
	int n, d, seed;

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(d)));

		if (modelVariant("element")) {
			Var i = var("i", dom(range(n)));
			Var v = var("v", dom(range(d)));
			((Problem) imp()).addCtr(CtrExtensionSmart.buildElement(((Problem) imp()), (Variable[]) x, (Variable) i, (Variable) v));
		}
		if (modelVariant("lex")) {
			Var[] y = array("y", size(n), dom(range(d)));
			((Problem) imp()).addCtr(CtrExtensionSmart.buildLexicographicL(((Problem) imp()), (Variable[]) x, (Variable[]) y, true));
		}
		if (modelVariant("max")) {
			Var m = var("m", dom(range(d)));
			((Problem) imp()).addCtr(CtrExtensionSmart.buildMaximum(((Problem) imp()), (Variable[]) x, (Variable) m));
		}
		if (modelVariant("notall")) {
			((Problem) imp()).addCtr(CtrExtensionSmart.buildNotAllEqual(((Problem) imp()), (Variable[]) x));
		}
		if (modelVariant("atmost1")) {
			Var v = var("v", dom(range(d)));
			((Problem) imp()).addCtr(CtrExtensionSmart.buildAtMost1(((Problem) imp()), (Variable[]) x, (Variable) v));
		}
		if (modelVariant("distinctv")) {
			Var[] y = array("y", size(n), dom(range(d)));
			((Problem) imp()).addCtr(CtrExtensionSmart.buildDistinctVectors(((Problem) imp()), (Variable[]) x, (Variable[]) y));
		}

		if (modelVariant("random")) {
			Random random = new Random(seed);
			SmartTuple[] smartTuples = new SmartTuple[6];
			for (int k = 0; k < smartTuples.length; k++) {
				List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
				for (int i = 0; i < x.length; i++) {
					int r = random.nextInt(9);
					if (r != 0) {
						if (r == 1)
							restrictions.add(eq(x[i], random.nextInt(d)));
						if (r == 2)
							restrictions.add(ne(x[i], random.nextInt(d)));
						if (r == 3)
							restrictions.add(lt(x[i], random.nextInt(d)));
						if (r == 4)
							restrictions.add(gt(x[i], random.nextInt(d)));
						int j = random.nextInt(n);
						if (j < i) { // if (i != j) {
							Var y = i > j ? x[i] : x[j];
							Var z = i > j ? x[j] : x[i];
							if (r == 5)
								restrictions.add(eq(y, z));
							if (r == 6)
								restrictions.add(ne(y, z));
							if (r == 7)
								restrictions.add(lt(y, z));
							if (r == 8)
								restrictions.add(gt(y, z));
						}
					}
				}
				smartTuples[k] = new SmartTuple(restrictions);

			}
			CtrExtensionSmart c = (CtrExtensionSmart) ((Problem) imp()).smart(x, smartTuples).ctr;
			System.out.println();
			for (SmartTuple t : c.smartTuples)
				System.out.println(t);
		}

		// if (isModel("smart"))
		// ((Problem) imp()).smart(x, new SmartTuple(eq(x[0], x[n - 1])), new SmartTuple(eq(x[1], x[n - 2])), new SmartTuple(lt(x[2],
		// x[3])));
		// ((Problem) imp()).smart(x, new SmartTuple(ge(x[0], add(x[n - 1], 5))), new SmartTuple(ge(x[n - 1], add(x[0], 3))),
		// new SmartTuple(eq(x[2], 0), eq(x[3], 0)));
		// ((Problem) imp()).smart(x, new SmartTuple(lt(x[0], x[1]), gt(x[2], x[3]), lt(x[4], x[5])),
		// new SmartTuple(eq(x[0], 0), eq(x[1], x[2]), gt(x[3], x[4]), gt(x[n - 1], 2)));
	}
}
