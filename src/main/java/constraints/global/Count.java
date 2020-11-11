package constraints.global;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;

import constraints.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import problem.Problem;
import utility.Kit;
import utility.sets.SetSparse;
import variables.Variable;
import variables.domains.Domain;

public abstract class Count extends CtrGlobal {

	public static Count buildFrom(Problem pb, Variable[] scp, int value, TypeConditionOperatorRel op, int k) {
		switch (op) {
		case LT:
			return new AtMostK(pb, scp, value, k - 1);
		case LE:
			return new AtMostK(pb, scp, value, k);
		case GE:
			return new AtLeastK(pb, scp, value, k);
		case GT:
			return new AtLeastK(pb, scp, value, k + 1);
		case EQ:
			return new ExactlyK(pb, scp, value, k);
		default:
			throw new AssertionError("NE is not implemented"); // TODO useful to have a propagator?
		}
	}

	/**
	 * The value that must be counted in the scope of the constraint.
	 */
	protected final int value;

	/**
	 * The right-operand used in the comparison (i.e., the number of occurrences used as limit).
	 */
	protected final int k;

	public Count(Problem pb, Variable[] list, int value, int k) {
		super(pb, list);
		this.value = value;
		this.k = k;
		defineKey(value, k);
		Kit.control(0 < k && k < list.length, () -> "Bad value of k=" + k);
		Kit.control(Stream.of(list).allMatch(x -> x.dom.isPresentValue(value) && x.dom.size() > 1), () -> "Badly formed scope.");
	}

	// ************************************************************************
	// ***** Constraint AtMostK
	// ************************************************************************

	public static class AtMostK extends Count implements TagSymmetric, TagGACGuaranteed, TagFilteringPartialAtEachCall {

		@Override
		public boolean checkValues(int[] t) {
			return Kit.countIn(value, t) <= k;
		}

		public AtMostK(Problem pb, Variable[] list, int value, int k) {
			super(pb, list, value, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (!x.dom.onlyContainsValue(value))
				return true;
			int cnt = 0;
			for (Variable y : scp)
				if (y.dom.onlyContainsValue(value) && ++cnt > k)
					return x.dom.fail(); // inconsistency detected
			if (cnt == k) {
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() > 1)
						dom.removeValueIfPresent(value);
				}
				// for (Variable y : scp)
				// if (y.dom.size() > 1)
				// y.dom.removeValueSafelyIfPresent(value);
			}
			return true;
		}
	}

	// ************************************************************************
	// ***** Constraint AtMost1
	// ************************************************************************

	public static final class AtMost1 extends AtMostK {

		public AtMost1(Problem pb, Variable[] list, int value) {
			super(pb, list, value, 1);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (!x.dom.onlyContainsValue(value))
				return true;
			for (Variable y : scp)
				if (y != x && !y.dom.removeValueIfPresent(value))
					return false;
			return true;
		}
	}
	// ************************************************************************
	// ***** Constraint AtLeastK
	// ************************************************************************

	public static class AtLeastK extends Count implements TagSymmetric, TagGACGuaranteed, TagFilteringPartialAtEachCall {

		@Override
		public boolean checkValues(int[] t) {
			return Kit.countIn(value, t) >= k;
		}

		/**
		 * Used for storing (k+1) sentinels ; stored values correspond to variable positions
		 */
		protected SetSparse sentinels;

		public AtLeastK(Problem pb, Variable[] list, int value, int k) {
			super(pb, list, value, k);
			if (k > 1) {
				sentinels = new SetSparse(list.length);
				IntStream.range(0, k + 1).forEach(i -> sentinels.add(i)); // k+1 sentinels
			}
		}

		@Override
		public boolean runPropagator(Variable x) {
			int p = positionOf(x);
			if (!sentinels.isPresent(p) || x.dom.isPresentValue(value))
				return true;
			// we search for another sentinel
			int[] dense = sentinels.dense;
			for (int i = sentinels.limit + 1; i < dense.length; i++)
				if (scp[dense[i]].dom.isPresentValue(value)) {
					sentinels.swap(p, dense[i]);
					return true;
				}
			// no new sentinel found ; we have to assign all k remaining variables
			for (int i = sentinels.limit; i >= 0; i--)
				if (dense[i] != p && scp[dense[i]].dom.reduceToValue(value) == false)
					return false;
			return true;
		}
	}

	// ************************************************************************
	// ***** Constraint AtLeast1
	// ************************************************************************

	public static final class AtLeast1 extends AtLeastK {

		/** Two sentinels for tracking the presence of the value. */
		private Variable sentinel1, sentinel2;

		public AtLeast1(Problem pb, Variable[] list, int value) {
			super(pb, list, value, 1);
			sentinel1 = list[0];
			sentinel2 = list[1];
		}

		private Variable findAnotherSentinel() {
			for (Variable x : scp)
				if (x != sentinel1 && x != sentinel2 && x.dom.isPresentValue(value))
					return x;
			return null;
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x == sentinel1) {
				if (!sentinel1.dom.isPresentValue(value)) {
					Variable sentinel = findAnotherSentinel();
					if (sentinel != null)
						sentinel1 = sentinel;
					else if (sentinel2.dom.reduceToValue(value) == false)
						return false;
				}
			} else if (x == sentinel2) {
				if (!sentinel2.dom.isPresentValue(value)) {
					Variable sentinel = findAnotherSentinel();
					if (sentinel != null)
						sentinel2 = sentinel;
					else if (sentinel1.dom.reduceToValue(value) == false)
						return false;
				}
			}
			return true;
		}
	}

	// ************************************************************************
	// ***** Constraint ExactlyK
	// ************************************************************************

	/**
	 * Exactly k variables of the scope, where k is a constant, must be assigned to the specified value.
	 * 
	 */
	public static class ExactlyK extends Count implements TagSymmetric, TagGACGuaranteed, TagFilteringCompleteAtEachCall {

		@Override
		public boolean checkValues(int[] t) {
			return Kit.countIn(value, t) == k;
		}

		public ExactlyK(Problem pb, Variable[] list, int value, int k) {
			super(pb, list, value, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			// nGuaranteedOccurrences denotes the number of singleton domains with the specified value
			// nPossibleOccurrences denotes the number of domains containing the specified value
			int nGuaranteedOccurrences = 0, nPossibleOccurrences = 0;
			for (Variable y : scp)
				if (y.dom.isPresentValue(value)) {
					nPossibleOccurrences++;
					if (y.dom.size() == 1 && ++nGuaranteedOccurrences > k)
						return y.dom.fail();
				}
			if (nGuaranteedOccurrences == k) {
				// remove value from all non singleton domains
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() > 1) // && dom.isPresentValue(value))
						dom.removeValueIfPresent(value);
				}
				return true;
			}
			if (nPossibleOccurrences < k)
				return x.dom.fail(); // inconsistency detected
			if (nPossibleOccurrences == k) {
				// assign all non singleton domains containing the value
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() > 1 && dom.isPresentValue(value))
						dom.reduceToValue(value);
				}
			}
			return true;
		}
	}

	// ************************************************************************
	// ***** Constraint Exactly1
	// ************************************************************************

	public static final class Exactly1 extends ExactlyK {

		public Exactly1(Problem pb, Variable[] list, int value) {
			super(pb, list, value, 1);
		}
	}

}
