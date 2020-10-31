/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
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

/*
 * "Rectangle packing problem." + "\nSee Simonis and O'Sullivan. Search strategies for rectangle packing. In Proceedings of CP 2008." +
 * "\nAlso used in short supports papers."
 */
public class RectPacking implements ProblemAPI {
	Rectangle container;
	Rectangle[] boxes;

	class Rectangle {
		int width, height;
	}

	@Override
	public void model() {
		int nBoxes = boxes.length;

		Var[] x = array("x", size(nBoxes), dom(range(container.width)), "x[i] is the x-coordinate where is put the ith rectangle");
		Var[] y = array("y", size(nBoxes), dom(range(container.height)), "y[i] is the y-coordinate where is put the ith rectangle");

		forall(range(nBoxes), i -> lessEqual(add(x[i], boxes[i].width), container.width)).note("unary constraints on x");
		forall(range(nBoxes), i -> lessEqual(add(y[i], boxes[i].height), container.height)).note("unary constraints on y");

		noOverlap(transpose(x, y), Stream.of(boxes).map(b -> tuple(b.width, b.height)).toArray(int[][]::new)).note("no overlap on boxes");

		// breaking symmetries ; see in "Search strategies for rectangle packing". Below, to be controlled
		if (container.width == container.height)
			block(() -> {
				lessEqual(x[nBoxes - 1], (int) Math.floor((container.width - boxes[nBoxes - 1].width) / 2.0));
				lessEqual(y[nBoxes - 1], x[nBoxes - 1]);
			}).tag(SYMMETRY_BREAKING);

		// if (imp() instanceof Problem)
		// ((Problem) imp()).annotateVarhStatic(
		// IntStream.range(0, nBoxes * 2).mapToObj(i -> i % 2 == 0 ? x[nBoxes - 1 - i / 2] : y[nBoxes - 1 - i / 2]).toArray(Variable[]::new));
	}
}
