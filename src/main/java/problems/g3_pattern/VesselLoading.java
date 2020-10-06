package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

// CSPLIb 08
public class VesselLoading implements ProblemAPI {

	int containerWidth;
	int containerHeight;
	Container[] containers;
	int[][] separations;

	class Container {
		int width, height, type;
	}

	Table shortTable(int i, int j, int separation) {
		Table table = table();
		// horizontal, i before j
		int min = Math.min(containers[i].width, containers[i].height);
		int max = Math.max(containers[i].width, containers[i].height);

		for (int xi = 0; xi < containerWidth - min; xi++) {
			for (int k = min; k < max; k++)
				table.add(xi, min, xi + k + separation, STAR, STAR, STAR, STAR, STAR);
			for (int xj = xi + max + separation; xj < containerWidth; xj++)
				table.add(xi, STAR, xj, STAR, STAR, STAR, STAR, STAR);
		}
		return table;
	}

	@Override
	public void model() {
		int nContainers = containers.length;

		Var[] x = array("x", size(nContainers), dom(range(containerWidth)), "x[i] is the x-coordinate of the ith container");
		Var[] y = array("y", size(nContainers), dom(range(containerHeight)), "y[i] is the y-coordinate of the ith container");
		Var[] w = array("w", size(nContainers), i -> dom(containers[i].width, containers[i].height), "w[i] is the width of the ith container");
		Var[] h = array("h", size(nContainers), i -> dom(containers[i].width, containers[i].height), "h[i] is the height of the ith container");
		Var[] r = array("r", size(nContainers), dom(0, 1), "r[i] is 1 iff the ith container is rotated by 90 degrees");

		forall(range(nContainers), i -> lessEqual(add(x[i], w[i]), containerWidth)).note("horizontal control");
		forall(range(nContainers), i -> lessEqual(add(y[i], h[i]), containerHeight)).note("vertical control");
		forall(range(nContainers), i -> {
			Table table = table(0, containers[i].width, containers[i].height).add(1, containers[i].height, containers[i].width);
			extension(vars(r[i], w[i], h[i]), table);
		}).note("managing rotation");
		noOverlap(transpose(x, y), transpose(w, h)).note("no overlapping between rectangles");
	}
}
