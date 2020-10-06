/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension;

import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import problem.Problem;
import propagation.order1.MaxRPWC;
import propagation.order1.MaxRPWC.Intersection;
import propagation.order1.MaxRPWC.Intersection.Leaf;
import utility.Kit;
import utility.sets.SetDense;
import utility.sets.SetSparse;
import variables.Variable;

public class CtrExtensionRPWC extends CtrExtensionSTR1 {

	/**
	 * The different intersections where the constraint occurs.
	 */
	protected Intersection[] intersections;

	/**
	 * intersectionPositions[i] gives the position of the constraint in intersections[i]
	 */
	private int[] intersectionPositions;

	private int[] lastTargetTimes; // the last time we used stamps for each associated constraint (in intersections)

	protected int lastCallTime; // the time of the last filtering call with this constraint

	private SetDense intersectionsToBeChecked;

	private SetSparse leavesToBeUpdated;

	private boolean test = false; // true;

	public void addIntersections(List<Intersection> list) {
		intersections = list.toArray(new Intersection[list.size()]);
		intersectionPositions = IntStream.range(0, intersections.length).map(i -> Utilities.indexOf(this, intersections[i].ctrs)).toArray();
		lastTargetTimes = Kit.repeat(-1, intersections.length);
		intersectionsToBeChecked = new SetDense(intersections.length);
		leavesToBeUpdated = new SetSparse(intersections.length, true);
	}

	public CtrExtensionRPWC(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	protected final boolean checkStampsFor(int[] tuple) {
		if (intersections == null)
			return true;
		if (test)
			leavesToBeUpdated.fill();
		for (int cursor = intersectionsToBeChecked.limit; cursor >= 0; cursor--) {
			int i = intersectionsToBeChecked.dense[cursor];
			int source = intersectionPositions[i], target = source == 0 ? 1 : 0; // only valid for binary intersections// TODO
			Leaf leaf = intersections[i].getLeafFor(tuple, source);
			if (leaf.stamps[target] != intersections[i].ctrs[target].lastCallTime)
				return false;
			else if (test && leaf.stamps[source] == lastCallTime)
				leavesToBeUpdated.remove(i);
		}
		// we have to update the stamps associated with the constraint
		if (test)
			for (int cursor = leavesToBeUpdated.limit; cursor >= 0; cursor--) {
				int i = leavesToBeUpdated.dense[cursor];
				int source = intersectionPositions[i];
				intersections[i].getLeafFor(tuple, source).stamps[source] = lastCallTime;
			}
		else
			for (int i = 0; i < intersections.length; i++) {
				int source = intersectionPositions[i];
				intersections[i].getLeafFor(tuple, source).stamps[source] = lastCallTime;
			}
		assert controlStamps(tuple);
		return true;
	}

	private boolean controlStamps(int[] tuple) {
		return IntStream.range(0, intersections.length).allMatch(i -> intersections[i].getLeafFor(tuple,
				intersectionPositions[i]).stamps[intersectionPositions[i]] == lastCallTime);
	}

	protected final void setIntersectionsToBeChecked() {
		MaxRPWC maxRPWC = (MaxRPWC) pb.solver.propagation;
		if (intersections != null) {
			lastCallTime = maxRPWC.incrementSpecificTime();
			intersectionsToBeChecked.clear();
			// if (denseSetOfTuples.getCurrentLimit() > 100)
			for (int i = 0; i < intersections.length; i++) {
				int target = intersectionPositions[i] == 0 ? 1 : 0; // because only binary intersections are handled currently
				if (intersections[i].ctrs[target].lastCallTime > maxRPWC.lastBacktrackSpecificTime
						&& lastTargetTimes[i] != intersections[i].ctrs[target].lastCallTime)
					intersectionsToBeChecked.add(i);
			}
		}
	}

	protected final void updateLastTargetTimes() {
		if (intersections != null)
			for (int cursor = intersectionsToBeChecked.limit; cursor >= 0; cursor--) {
				int i = intersectionsToBeChecked.dense[cursor];
				int target = intersectionPositions[i] == 0 ? 1 : 0;
				lastTargetTimes[i] = intersections[i].ctrs[target].lastCallTime;
			}
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		pb.stuff.updateStatsForSTR(set);
		int depth = pb.solver.depth();
		beforeFiltering();
		setIntersectionsToBeChecked();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple) && checkStampsFor(tuple))
				for (int j = futvars.limit; j >= 0; j--) {
					int x = futvars.dense[j];
					int a = tuple[x];
					if (!ac[x][a]) {
						cnt--;
						cnts[x]--;
						ac[x][a] = true;
					}
				}
			else
				set.removeAtPosition(i, depth);
		}
		updateLastTargetTimes();
		return updateDomains();
	}
}

// private boolean checkStampsFor(int[] tuple) {
// for (int i = 0; i < intersections.length; i++) {
// int source = intersectionPositions[i], target = source == 0 ? 1 : 0; // only valid for binary intersections TODO
// Leaf l = intersections[i].getLeafFor(tuple, source);
// // Kit.prn("search " + this + " " + source + " t=" + Kit.implode(tuple) + " " + intersections[i]);
// int stamp = l.stamps[target];
// if (stamp > maxRPWC.lastBacktrackTime && stamp != intersections[i].constraints[target].lastCallTime)
// return false;
// }
// for (int i = 0; i < intersections.length; i++) {
// int source = intersectionPositions[i];
// intersections[i].getLeafFor(tuple, source).stamps[source] = lastCallTime;
// }
// return true;
// }