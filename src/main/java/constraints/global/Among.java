package constraints.global;

import static utility.Kit.control;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class Among extends ConstraintGlobal implements TagSymmetric, TagAC, TagCallCompleteFiltering {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		int cnt = 0;
		for (int v : t)
			if (values.contains(v))
				cnt++;
		return cnt == k;
		// return IntStream.of(t).filter(v -> values.contains(v)).count() == k;
	}

	/**
	 * The values that must be counted in the list of the constraint.
	 */
	private final Set<Integer> values;

	private final int k;

	/**
	 * A set used temporarily when filtering
	 */
	private final SetSparse mixedVariables;

	public Among(Problem pb, Variable[] list, int[] values, int k) {
		super(pb, list);
		this.values = IntStream.of(values).boxed().collect(Collectors.toCollection(HashSet::new)); // TODO HashSet better than TreeSet, right?
		this.k = k;
		this.mixedVariables = new SetSparse(list.length);
		defineKey(Kit.join(values), k);
		control(Kit.isStrictlyIncreasing(values), "Values must be given in increasing order");
		control(0 < k && k < list.length, "Bad value of k=" + k);
		control(Stream.of(list).allMatch(x -> x.dom.size() > 1 && IntStream.of(values).anyMatch(v -> x.dom.containsValue(v))), "Badly formed scope.");
	}

	@Override
	public boolean runPropagator(Variable x) {
		int nGuaranteedVars = 0, nPossibleVars = 0;
		mixedVariables.clear();
		for (int i = 0; i < scp.length; i++) {
			Domain dom = scp[i].dom;
			boolean atLeastOnePresentValue = false, atLeastOneAbsentValue = false;
			for (int a = dom.first(); a != -1 && (!atLeastOnePresentValue || !atLeastOneAbsentValue); a = dom.next(a)) {
				boolean b = values.contains(dom.toVal(a));
				atLeastOnePresentValue = atLeastOnePresentValue || b;
				atLeastOneAbsentValue = atLeastOneAbsentValue || !b;
			}
			if (atLeastOnePresentValue) {
				nPossibleVars++;
				if (!atLeastOneAbsentValue && ++nGuaranteedVars > k)
					return dom.fail(); // inconsistency detected
				if (atLeastOneAbsentValue)
					mixedVariables.add(i);
			}
		}
		if (nGuaranteedVars == k) {
			for (int i = mixedVariables.limit; i >= 0; i--)
				scp[mixedVariables.dense[i]].dom.removeValuesIn(values); // no inconsistency possible
			return entailed();
		}
		if (nPossibleVars < k)
			return x.dom.fail();
		if (nPossibleVars == k) {
			for (int i = mixedVariables.limit; i >= 0; i--)
				scp[mixedVariables.dense[i]].dom.removeValuesNotIn(values); // no inconsistency possible
			return entailed();
		}
		return true;
	}

}
