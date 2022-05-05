/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static utility.Kit.control;

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import sets.SetDense;
import variables.Domain;
import variables.Variable;

/**
 * This constraint NoOverlap ensures that items defined as rectangles of various sizes do not overlap.
 * 
 * @author Christophe Lecoutre
 */
public final class NoOverlap extends ConstraintGlobal implements TagNotAC, TagCallCompleteFiltering {

	@Override
	public boolean isSatisfiedBy(int[] tuple) {
		for (int i = 0; i < half; i++)
			for (int j = i + 1; j < half; j++) {
				int xi = tuple[i], xj = tuple[j], yi = tuple[i + half], yj = tuple[j + half];
				if (!(xi + widths[i] <= xj || xj + widths[j] <= xi || yi + heights[i] <= yj || yj + heights[j] <= yi))
					return false;
			}
		return true;
	}

	/**
	 * xs[i] is the position of the ith item along the x-axis
	 */
	private final Variable[] xs;

	/**
	 * widths[i] is the width of the ith item
	 */
	private final int[] widths;

	/**
	 * ys[i] is the position of the ith item along the y-axis
	 */
	private final Variable[] ys;

	/**
	 * heights[i] is the height of the ith item
	 */
	private final int[] heights;

	/**
	 * The number of items (half of the scope size)
	 */
	private final int half;

	private final SetDense overlappings;

	private int[][] residues1;
	private int[][] residues2;

	public NoOverlap(Problem pb, Variable[] xs, int[] widths, Variable[] ys, int[] heights) {
		super(pb, Utilities.collect(Variable.class, xs, ys));
		control(xs.length > 1 && xs.length == widths.length && ys.length == heights.length && xs.length == ys.length);
		control(scp.length == xs.length + ys.length);
		this.xs = xs;
		this.widths = widths;
		this.ys = ys;
		this.heights = heights;
		this.half = xs.length;
		this.overlappings = new SetDense(half);
		this.residues1 = Variable.litterals(xs).intArray();
		this.residues2 = Variable.litterals(ys).intArray();
	}

	private boolean overlap(int a, Domain dom, int b) {
		return a > dom.lastValue() && dom.firstValue() > b;
	}

	private boolean findSupport(Variable[] x1, int[] t1, Variable[] x2, int[] t2, int w, int ww) { // ww = w + t2[i]
		long volume = 0;
		int minX = Integer.MAX_VALUE, minY = Integer.MAX_VALUE;
		int maxX = Integer.MIN_VALUE, maxY = Integer.MIN_VALUE;
		for (int k = overlappings.limit; k >= 0; k--) {
			int j = overlappings.dense[k];
			if (overlap(ww, x2[j].dom, w - t2[j]))
				return false; // to try another value w
			minX = Math.min(minX, x1[j].dom.firstValue());
			minY = Math.min(minY, x2[j].dom.firstValue());
			maxX = Math.max(maxX, x1[j].dom.lastValue() + t1[j]);
			maxY = Math.max(maxY, x2[j].dom.lastValue() + t2[j]);
			volume += t1[j] * t2[j];
		}
		int diffX = maxX - minX + 1, diffY = maxY - minY + 1;
		// we can remove up to t2[i] at diffY because there may be no possible overlapping on x along
		// this height
		if (w < minY && minY < ww)
			diffY -= Math.min(maxY, ww) - minY;
		else if (minY <= w && w < maxY)
			diffY -= Math.min(maxY, ww) - w;
		if (volume > diffX * diffY) // not enough room for the items
			return false; // to try another value w
		return true; // because found support
	}

	// TODO: some optimizations of the code are apparently possible
	public boolean filter(Variable[] x1, int[] t1, Variable[] x2, int[] t2, int[][] residues) {
		for (int i = 0; i < half; i++) {
			Domain dom1 = x1[i].dom;
			extern: for (int a = dom1.first(); a != -1; a = dom1.next(a)) {
				int v = dom1.toVal(a); // we are going to look for a support of (x1[i],v)
				// we compute the set of tasks overlapping on the first axis wrt (x1[i],v)
				overlappings.clear();
				for (int j = 0; j < half; j++)
					if (j != i && overlap(v + t1[i], x1[j].dom, v - t1[j]))
						overlappings.add(j);
				if (overlappings.size() == 0)
					continue;
				if (overlappings.size() == 1) {
					int j = overlappings.dense[0];
					if (!overlap(x2[i].dom.firstValue() + t2[i], x2[j].dom, x2[i].dom.lastValue() - t2[j]))
						continue;
					// otherwise it means that overlapping is present on both dimensions (so, there is no support for
					// (x1[i],v))
				} else {
					// we now look for a value w in the domain of x2[i] that is compatible with first axis overlapping
					// boxes
					// a kind of k-wise consistency is used (see paper about sweep for information about the principle)
					// also, a local form of energetic reasoning is used
					Domain dom2 = x2[i].dom;
					int residue = residues[i][a];
					if (dom2.contains(residue)) {
						int w = dom2.toVal(residue);
						if (findSupport(x1, t1, x2, t2, w, w + t2[i]))
							continue extern;
					}
					for (int b = dom2.first(); b != -1; b = dom2.next(b)) {
						if (b == residue)
							continue;
						int w = dom2.toVal(b);
						if (findSupport(x1, t1, x2, t2, w, w + t2[i])) {
							residues[i][a] = b;
							continue extern;
						}
					}
				}
				// at this step, no support has been found
				if (dom1.remove(a) == false)
					return false;
			}
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable x) {
		return filter(xs, widths, ys, heights, residues1) && filter(ys, heights, xs, widths, residues2);
	}
}

// System.out.println("volume " + volume + " size=" + set.size() + " surface=" + surface + "
// xi=" + v + " yi=" + w);
// for (int k = set.limit; k >= 0; k--) {
// int j = set.dense[k];
// System.out.println("xi=" + j + " " + x1[j].dom.firstValue() + ".." +
// x1[j].dom.lastValue() + " (" + t1[j] + ")");
// System.out.println("yj=" + j + " " + x2[j].dom.firstValue() + ".." +
// x2[j].dom.lastValue() + " (" + t2[j] + ")");
// }
// System.out.println("minX=" + minX + " maxX=" + maxX + " minY=" + minY + " maxY=" + maxY +
// " t2i=" + t2[i]);
