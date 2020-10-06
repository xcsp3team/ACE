package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class StripPacking implements ProblemAPI {

	Rectangle container;
	Rectangle[] rectangles;

	class Rectangle {
		int width, height;
	}

	@Override
	public void model() {
		int nRectangles = rectangles.length;

		Var[] x = array("x", size(nRectangles), dom(range(container.width)), "x[i] is the x-coordinate of the ith rectangle");
		Var[] y = array("y", size(nRectangles), dom(range(container.height)), "y[i] is the y-coordinate of the ith rectangle");
		Var[] w = array("w", size(nRectangles), i -> dom(rectangles[i].width, rectangles[i].height), "w[i] is the width of the ith rectangle");
		Var[] h = array("h", size(nRectangles), i -> dom(rectangles[i].width, rectangles[i].height), "h[i] is the height of the ith rectangle");
		Var[] r = array("r", size(nRectangles), dom(0, 1), "r[i] is 1 iff the ith rectangle is rotated by 90 degrees");

		forall(range(nRectangles), i -> lessEqual(add(x[i], w[i]), container.width)).note("horizontal control");
		forall(range(nRectangles), i -> lessEqual(add(y[i], h[i]), container.height)).note("vertical control");
		forall(range(nRectangles), i -> {
			Table table = table(0, rectangles[i].width, rectangles[i].height).add(1, rectangles[i].height, rectangles[i].width);
			extension(vars(r[i], w[i], h[i]), table);
		}).note("managing rotation");
		noOverlap(transpose(x, y), transpose(w, h)).note("no overlapping between rectangles");
	}
}
