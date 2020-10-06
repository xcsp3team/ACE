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

public class Optim implements ProblemAPI {

	@Override
	public void model() {
		Var x = var("x", dom(rangeClosed(1, 10)));
		Var y = var("y", dom(rangeClosed(1, 10)));
		Var z = var("z", dom(rangeClosed(1, 10)));

		intension(lt(x, y));
		intension(lt(y, z));

		maximize(SUM, vars(x, y, z));
	}
}