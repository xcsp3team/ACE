package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Range;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

// 6 solutions for dingbas
public class CarSequencing implements ProblemAPI {

	CarClass[] classes;
	OptionLimit[] limits;

	class CarClass {
		int demand;
		int[] options;
	}

	class OptionLimit {
		int num, den;
	}

	private Table channelingTable() {
		Table table = table();
		for (int i = 0; i < classes.length; i++)
			table.add(i, classes[i].options); // indexing car class options
		return table;
	}

	@Override
	public void model() {
		int[] demands = valuesFrom(classes, c -> c.demand);
		int nCars = sumOf(demands), nOptions = limits.length, nClasses = classes.length;
		Range allClasses = range(nClasses);

		Var[] c = array("c", size(nCars), dom(allClasses), "c[i] is the class of the ith assembled car");
		Var[][] o = array("o", size(nCars, nOptions), dom(0, 1), "o[i][k] is 1 if the ith assembled car has option k");

		cardinality(c, allClasses, occurExactly(demands)).note("building the right numbers of cars per class");

		if (modelVariant(""))
			forall(range(nCars).range(nClasses).range(nOptions), (i, j, k) -> implication(eq(c[i], j), eq(o[i][k], classes[j].options[k])))
					.note("constraints about options");
		else if (modelVariant("table")) {
			Table table = channelingTable();
			forall(range(nCars), i -> extension(vars(c[i], o[i]), table)).note("constraints about options");
		}

		forall(range(nOptions).range(nCars), (k, i) -> {
			if (i <= nCars - limits[k].den)
				sum(select(columnOf(o, k), range(i, i + limits[k].den)), LE, limits[k].num);
		}).note("constraints about option frequencies");

		forall(range(nOptions).range(nCars), (k, i) -> {
			// i stands for the number of blocks set to the maximal capacity
			int nOptionOccurrences = sumOf(valuesFrom(classes, cl -> cl.options[k] * cl.demand));
			int nOptionsRemainingToSet = nOptionOccurrences - i * limits[k].num;
			int nOptionsPossibleToSet = nCars - i * limits[k].den;
			if (nOptionsRemainingToSet > 0 && nOptionsPossibleToSet > 0)
				sum(select(columnOf(o, k), range(nOptionsPossibleToSet)), GE, nOptionsRemainingToSet);
		}).tag(REDUNDANT_CONSTRAINTS);
	}
}

// sum(select(o, (j, l) -> i <= j && j < i + limits[k].den && l == k), LE, limits[k].num);

// int[] nOptionOccurrences = range(nOptions).map(i -> IntStream.range(0, nClasses).map(j -> classes[j].options[i] *
// classes[j].demand).sum());

// Table table = table().add(range(nClasses).provideTuples(i -> tuple(i, classes[i].options)));
// int[][] tuples = range(nClasses).provideTuples(i -> tuple(i, classes[i].options));
