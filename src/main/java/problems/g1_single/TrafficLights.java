/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import org.xcsp.common.IVar.VarSymbolic;
import org.xcsp.common.structures.TableSymbolic;
import org.xcsp.modeler.api.ProblemAPI;

// not interesting for n> 4 because trivial
public class TrafficLights implements ProblemAPI {

	@Override
	public void model() {
		String RED = "red", RED_YELLOW = "red-yellow", GREEN = "green", YELLOW = "yellow";

		VarSymbolic[] v = arraySymbolic("v", size(4), dom(GREEN, RED, RED_YELLOW, YELLOW), "v[i] is the color for the ith vehicle traffic light");
		VarSymbolic[] p = arraySymbolic("p", size(4), dom(GREEN, RED), "p[i] is the color for the ith pedestrian traffic light");

		TableSymbolic table = tableSymbolic().add(RED, RED, GREEN, GREEN).add(RED_YELLOW, RED, YELLOW, RED).add(GREEN, GREEN, RED, RED).add(YELLOW, RED,
				RED_YELLOW, RED);
		forall(range(4), i -> extension(vars(v[i], p[i], v[(i + 1) % 4], p[(i + 1) % 4]), table));
	}
}
