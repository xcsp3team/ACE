/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import org.xcsp.common.Utilities;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import variables.Variable;

public final class NoOverlap extends CtrGlobal implements TagNotAC {

	@Override
	public boolean checkValues(int[] tuple) {
		for (int i = 0; i < x.length; i++)
			for (int j = i + 1; j < x.length; j++) {
				int xi = tuple[i], xj = tuple[j], yi = tuple[i + half], yj = tuple[j + half];
				if (!(xi + widths[i] <= xj || xj + widths[j] <= xi || yi + heights[i] <= yj || yj + heights[j] <= yi))
					return false;
			}
		return true;
	}

	private Variable[] x;
	int[] widths;
	Variable[] y;
	int[] heights;

	int half;

	public NoOverlap(Problem pb, Variable[] x, int[] widths, Variable[] y, int[] heights) {
		super(pb, Utilities.collect(Variable.class, x, y));
		control(x.length > 1 && x.length == widths.length && y.length == heights.length && x.length == y.length);
		control(scp.length == x.length + y.length);
		this.x = x;
		this.widths = widths;
		this.y = y;
		this.heights = heights;
		this.half = x.length;
	}

	@Override
	public boolean runPropagator(Variable x) {
		return true;
	}

	// public String toString() {
	// return "constraint cumulative: " + Kit.join(scp) + " lengths=" + Kit.join(this.lengths) + " heights=" + Kit.join(heights) + " limit=" + limit;
	// }

}
