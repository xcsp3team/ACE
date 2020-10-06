/**
 * ++ * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.extension.structures.SmartTuple;
import problem.Problem;

//  java abscon.Resolution problems.generators.BusSchedulingReaderZ c1.dzn -model=smt -r_n=40 => bound=31
public class BusScheduling implements ProblemAPI {
	int nTasks;
	int[][] shifts;

	@Override
	public void model() {
		int nShifts = shifts.length;

		if (modelVariant("")) {
			Var[] x = array("x", size(nShifts), dom(0, 1), "x[i] is 1 iff the ith shift is selected");
			forall(range(nTasks), t -> exactly(select(x, i -> contains(shifts[i], t)), takingValue(1), 1)).note("Each task is covered by exactly one shift");
			minimize(SUM, x);
		}
		if (modelVariant("smt")) {
			Var[] x = array("x", size(nTasks), t -> dom(range(nShifts).select(i -> contains(shifts[i], t))), "x[t] is the shift selected to perform task t");
			forall(range(nShifts), i -> {
				Var[] scp = select(x, shifts[i]);
				SmartTuple st1 = new SmartTuple(repeat(i, shifts[i].length));
				SmartTuple st2 = new SmartTuple(Stream.of(scp).map(y -> ne(y, i)));
				((Problem) imp()).smart(scp, st1, st2);
			}).note("a shift is selected for a task iff it is slected for each task it covers");
			minimize(NVALUES, x);
		}
	}
}
