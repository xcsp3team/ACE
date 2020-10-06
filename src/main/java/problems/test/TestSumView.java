/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class TestSumView implements ProblemAPI {

	@Override
	public void model() {
		Var[] x = array("x", size(5), dom(range(5)));

		sum(IntStream.range(0, x.length).mapToObj(i -> eq(x[i], i)), GT, 3);
	}
}
