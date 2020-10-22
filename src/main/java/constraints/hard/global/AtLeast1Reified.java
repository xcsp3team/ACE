package constraints.hard.global;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.hard.CtrGlobal;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public class AtLeast1Reified extends CtrGlobal implements ObserverBacktrackingSystematic, TagFilteringPartialAtEachCall, TagGACGuaranteed {

	@Override
	public boolean checkValues(int[] t) {
		boolean b = t[0] == 1;
		for (int i = 1; i < t.length; i++)
			if (t[i] == value)
				return b;
		return !b;
	}

	@Override
	public void restoreBefore(int depth) {
		entailed = false;
	}

	private final Variable[] list;
	private final int value;
	private final Variable reif;

	private Variable sentinel1, sentinel2;
	private boolean entailed;

	@Override
	public int[] defineSymmetryMatching() {
		return IntStream.range(0, scp.length).map(i -> i == 0 ? 1 : 2).toArray();
	}

	public AtLeast1Reified(Problem pb, Variable[] list, int value, Variable reif) {
		super(pb, pb.api.vars(reif, list));
		Kit.control(list.length >= 2 && Variable.areAllDistinct(list) && Variable.areAllInitiallyBoolean(reif));
		Stream.of(list).forEach(
				x -> Kit.control(x.dom.toPresentIdx(value) != -1, () -> x + " should not be in  " + this + " since its domain does not contain " + value));
		this.list = list;
		this.value = value;
		this.reif = reif;
		this.sentinel1 = list[0];
		this.sentinel2 = list[1];
	}

	private Variable findAnotherSentinel() {
		for (Variable x : scp)
			if (x != sentinel1 && x != sentinel2 && x.dom.isPresentValue(value))
				return x;
		return null;
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (entailed)
			return true;
		if (x == reif) {
			assert reif.dom.size() == 1;
			if (reif.dom.first() == 0) {
				for (Variable y : list)
					if (y.dom.removeValueIfPresent(value) == false)
						return false;
				return entailed = true;
			}
		} else if (x.dom.onlyContainsValue(value)) {
			if (reif.dom.removeValueIfPresent(0) == false)
				return false;
			return entailed = true;
		}
		if (reif.dom.size() == 2) { // just need one sentinel here
			if (!sentinel1.dom.isPresentValue(value)) {
				Variable sentinel = findAnotherSentinel();
				if (sentinel == null) {
					reif.dom.remove(1);
					return entailed = true;
				}
				sentinel1 = sentinel;
			}
		} else {
			assert reif.dom.first() == 1;
			if (!sentinel1.dom.isPresentValue(value)) {
				Variable sentinel = findAnotherSentinel();
				if (sentinel == null)
					return sentinel2.dom.reduceToValue(value) == false ? false : (entailed = true);
				sentinel1 = sentinel;
			}
			if (!sentinel2.dom.isPresentValue(value)) {
				Variable sentinel = findAnotherSentinel();
				if (sentinel == null)
					return sentinel1.dom.reduceToValue(value) == false ? false : (entailed = true);
				sentinel2 = sentinel;
			}
		}
		return true;
	}
}
