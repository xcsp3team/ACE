package constraints.global;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagFilteringPartialAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import variables.Domain;
import variables.Variable;

public abstract class Count extends CtrGlobal implements TagGACGuaranteed { // For the moment all inherited classes guarantee GAC

	public static int countIn(int value, int[] t, int from, int to) {
		int cnt = 0;
		for (int i = from; i < to; i++)
			if (t[i] == value)
				cnt++;
		return cnt;
	}

	public static int countIn(int value, int[] t) {
		int cnt = 0;
		for (int v : t)
			if (v == value)
				cnt++;
		return cnt;
	}

	/**
	 * The list where we count the value
	 */
	protected final Variable[] list;

	/**
	 * The value that must be counted in the list of the constraint.
	 */
	protected final int value;

	public Count(Problem pb, Variable[] scp, Variable[] list, int value) {
		super(pb, scp);
		this.list = list;
		this.value = value;
		control(Stream.of(list).allMatch(x -> x.dom.isPresentValue(value) && x.dom.size() > 1), () -> "Badly formed scope.");
	}

	/**********************************************************************************************
	 * CountCst
	 *********************************************************************************************/

	public static abstract class CountCst extends Count {

		public static CountCst buildFrom(Problem pb, Variable[] scp, int value, TypeConditionOperatorRel op, int k) {
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
		 * The right-operand used in the comparison (i.e., the number of occurrences used as limit).
		 */
		protected final int k;

		public CountCst(Problem pb, Variable[] list, int value, int k) {
			super(pb, list, list, value);
			this.k = k;
			defineKey(value, k);
			control(0 < k && k < list.length, () -> "Bad value of k=" + k);
		}

		// ************************************************************************
		// ***** Constraint AtMostK
		// ************************************************************************

		public static class AtMostK extends CountCst implements TagSymmetric, TagFilteringPartialAtEachCall {

			@Override
			public boolean checkValues(int[] t) {
				return countIn(value, t) <= k;
			}

			public AtMostK(Problem pb, Variable[] list, int value, int k) {
				super(pb, list, value, k);
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (!x.dom.onlyContainsValue(value))
					return true; // because we only filter when the recently filtered variable x has been assigned to the value
				int cnt = 0;
				for (Variable y : scp)
					if (y.dom.onlyContainsValue(value) && ++cnt > k)
						return x.dom.fail(); // inconsistency detected
				if (cnt == k) {
					for (int i = futvars.limit; i >= 0; i--) {
						Domain dom = scp[futvars.dense[i]].dom;
						if (dom.size() > 1)
							dom.removeValueIfPresent(value); // note that inconsistency is no more possible
					}
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

		public static class AtLeastK extends CountCst implements TagSymmetric, TagFilteringPartialAtEachCall {

			@Override
			public boolean checkValues(int[] t) {
				return countIn(value, t) >= k;
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
		public static class ExactlyK extends CountCst implements TagSymmetric, TagFilteringCompleteAtEachCall {

			@Override
			public boolean checkValues(int[] t) {
				return countIn(value, t) == k;
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
						if (dom.size() > 1)
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

	/**********************************************************************************************
	 * CountVar
	 *********************************************************************************************/

	public static abstract class CountVar extends Count {

		public static CountVar buildFrom(Problem pb, Variable[] scp, int value, TypeConditionOperatorRel op, Variable k) {
			switch (op) {
			case LT:
				throw new AssertionError();
			case LE:
				throw new AssertionError();
			case GE:
				throw new AssertionError();
			case GT:
				throw new AssertionError();
			case EQ:
				return new ExactlyVarK(pb, scp, value, k);
			default:
				throw new AssertionError("NE is not implemented");
			}
		}

		protected final Variable k;

		protected final int indexOfKInList; // -1 if not present

		public CountVar(Problem pb, Variable[] list, int value, Variable k) {
			super(pb, pb.vars(list, k), list, value);
			this.k = k;
			this.indexOfKInList = Utilities.indexOf(k, list);
			defineKey(value, indexOfKInList);
			// checking the domain of k ?
		}

		/**
		 * Exactly k variables of the specified vector of variables, where k is a variable, must be assigned to the specified value
		 * 
		 */
		public final static class ExactlyVarK extends CountVar implements TagFilteringCompleteAtEachCall {

			@Override
			public boolean checkValues(int[] t) {
				return indexOfKInList != -1 ? CountCst.countIn(value, t) == t[indexOfKInList] : CountCst.countIn(value, t, 0, t.length - 1) == t[t.length - 1];
			}

			@Override
			public int[] defineSymmetryMatching() {
				return IntStream.range(0, scp.length).map(i -> i == indexOfKInList || (indexOfKInList == -1 && i == scp.length - 1) ? 2 : 1).toArray();
			}

			public ExactlyVarK(Problem pb, Variable[] list, int value, Variable k) {
				super(pb, list, value, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// counting the nb of occurrences of value in list
				int nGuaranteedOccurrences = 0, nPossibleOccurrences = 0;
				for (Variable x : list)
					if (x.dom.isPresentValue(value)) {
						nPossibleOccurrences++;
						if (x.dom.size() == 1)
							nGuaranteedOccurrences++;
					}
				Domain domK = k.dom;
				if (domK.size() == 1) {
					int valK = domK.uniqueValue();
					if (valK < nGuaranteedOccurrences || nPossibleOccurrences < valK)
						return domK.fail();
				} else {
					// possible update of the domain of k when present in the vector, first by removing value (if present)
					// so as to update immediately nPossibleOccurrences
					if (indexOfKInList != -1) {
						int a = domK.toPresentIdx(value);
						if (a != -1) {
							boolean deleted = false;
							for (int b = domK.first(); b != -1; b = domK.next(b))
								if (b == a) {
									if (value < nGuaranteedOccurrences + 1 || nPossibleOccurrences < value) { // +1 by assuming we assign the value
										if (domK.remove(a) == false)
											return false;
										deleted = true;
									}
								} else {
									int v = domK.toVal(b);
									if (v < nGuaranteedOccurrences || nPossibleOccurrences - 1 < v) { // -1 by assuming we assign v (and not val)
										if (domK.remove(b) == false)
											return false;
									}
								}
							if (deleted)
								nPossibleOccurrences--;
						} else {
							if (domK.removeValuesLT(nGuaranteedOccurrences) == false || domK.removeValuesGT(nPossibleOccurrences) == false)
								return false;
						}
					} else if (domK.removeValuesLT(nGuaranteedOccurrences) == false || domK.removeValuesGT(nPossibleOccurrences) == false)
						return false;
				}
				// if k is singleton, updating the domain of the other variables
				if (domK.size() == 1) {
					int v = domK.uniqueValue();
					if (v == nGuaranteedOccurrences)
						for (Variable x : list)
							if (x.dom.size() > 1 && x.dom.isPresentValue(value))
								if (!x.dom.removeValue(value))
									return false;
					if (v == nPossibleOccurrences)
						for (Variable x : list)
							if (x.dom.size() > 1 && x.dom.isPresentValue(value))
								x.dom.reduceToValue(value);
				}
				return true;
			}
		}
	}

}
