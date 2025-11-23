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

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * The constraint Count imposes that the number of variables from a specified list of variables that take their values
 * from a specified set (but typically, the set only contains one value) respects a numerical condition. This constraint
 * captures known constraints (usually) called AtLeast, AtMost, Exactly and Among. The constraint Among is defined in a
 * separate file.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Count extends ConstraintGlobal implements TagAC {
	// For the moment all inherited classes guarantee AC

	/**
	 * The list where we have to count the number of occurrences of the value
	 */
	protected final Variable[] list;

	/**
	 * The value whose number of occurrences (in the list) must be counted
	 */
	protected final int value;

	/**
	 * Builds a constraint Count for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 * @param list
	 *            the list where counting is done
	 * @param value
	 *            the value whose number of occurrences must be counted
	 */
	public Count(Problem pb, Variable[] scp, Variable[] list, int value) {
		super(pb, scp);
		this.list = list;
		this.value = value;
		control(Stream.of(list).allMatch(x -> x.dom.containsValue(value)), "Badly formed scope " + value);
	}

	/**********************************************************************************************
	 * CountCst
	 *********************************************************************************************/

	/**
	 * Constraints Count where the right-hand operand (of the condition that must be respected) is a constant (integer)
	 */
	public static abstract class CountCst extends Count {

		public static CountCst buildFrom(Problem pb, Variable[] scp, int value, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return k == 2 ? new AtMost1(pb, scp, value) : new AtMostK(pb, scp, value, k - 1);
			case LE:
				return k == 1 ? new AtMost1(pb, scp, value) : new AtMostK(pb, scp, value, k);
			case GE:
				return k == 1 ? new AtLeast1(pb, scp, value) : new AtLeastK(pb, scp, value, k);
			case GT:
				return k == 0 ? new AtLeast1(pb, scp, value) : new AtLeastK(pb, scp, value, k + 1);
			case EQ:
				return k == 1 ? new Exactly1(pb, scp, value) : new ExactlyK(pb, scp, value, k);
			default:
				throw new AssertionError("NE is not implemented"); // TODO is it useful to implement a propagator?
			}
		}

		/**
		 * The right-operand used in the comparison (i.e., the number of occurrences used as a limit).
		 */
		protected final int k;

		/**
		 * Builds a constraint Count for the specified problem, with a limit (k) defined by a constant
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list
		 *            the list where counting is done
		 * @param value
		 *            the value whose number of occurrences must be counted
		 * @param k
		 *            the limit used for comparison in the right-operand
		 */
		public CountCst(Problem pb, Variable[] list, int value, int k) {
			super(pb, list, list, value);
			this.k = k;
			defineKey(value, k);
			control(0 < k && k < list.length, "Bad value for k: " + k);
			control(Stream.of(list).allMatch(x -> x.dom.size() > 1), "Badly formed scope");

		}

		// ************************************************************************
		// ***** Constraints AtMostK and AtMost1
		// ************************************************************************

		public static class AtMostK extends CountCst implements TagSymmetric { // not call filtering-complete

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Kit.countIn(value, t) <= k;
			}

			public AtMostK(Problem pb, Variable[] list, int value, int k) {
				super(pb, list, value, k);
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (!x.dom.containsOnlyValue(value))
					return true; // because we only filter when the recently filtered variable x has been assigned to the value
				int cnt = 0;
				for (Variable y : scp)
					if (y.dom.containsOnlyValue(value) && ++cnt > k)
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

		public static final class AtMost1 extends AtMostK {

			public AtMost1(Problem pb, Variable[] list, int value) {
				super(pb, list, value, 1);
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (!x.dom.containsOnlyValue(value))
					return true; // because we only filter when the recently filtered variable x has been assigned to the value
				for (Variable y : scp)
					if (y != x && y.dom.removeValueIfPresent(value) == false)
						return false;
				return entail();
			}
		}
		// ************************************************************************
		// ***** Constraints AtLeastK and AtLeast1
		// ************************************************************************

		public static class AtLeastK extends CountCst implements TagSymmetric { // not call filtering-complete

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Kit.countIn(value, t) >= k;
			}

			/**
			 * Used for storing (k+1) sentinels ; stored values correspond to variable positions
			 */
			protected SetSparse sentinels;

			public AtLeastK(Problem pb, Variable[] list, int value, int k) {
				super(pb, list, value, k);
				if (k > 1) {
					this.sentinels = new SetSparse(list.length);
					IntStream.range(0, k + 1).forEach(i -> sentinels.add(i)); // k+1 sentinels
				}
			}

			@Override
			public boolean runPropagator(Variable x) {
				int p = positionOf(x);
				if (!sentinels.contains(p) || x.dom.containsValue(value))
					return true;
				// we search for another sentinel
				int[] dense = sentinels.dense;
				for (int i = sentinels.limit + 1; i < dense.length; i++)
					if (scp[dense[i]].dom.containsValue(value)) { // another sentinel is found
						sentinels.swap(p, dense[i]);
						return true;
					}
				// no new sentinel found ; we have to assign all k remaining variables
				for (int i = sentinels.limit; i >= 0; i--)
					if (dense[i] != p && scp[dense[i]].dom.reduceToValue(value) == false)
						return false;
				return entail();
			}
		}

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
					if (x != sentinel1 && x != sentinel2 && x.dom.containsValue(value))
						return x;
				return null;
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x == sentinel1) {
					if (!sentinel1.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel1 = sentinel;
						else
							return sentinel2.dom.reduceToValue(value) && entail();
						// before, was: if (sentinel2.dom.reduceToValue(value) == false) return false;
					}
				} else if (x == sentinel2) {
					if (!sentinel2.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel2 = sentinel;
						else
							return sentinel1.dom.reduceToValue(value) && entail();
						// before was: if (sentinel1.dom.reduceToValue(value) == false) return false;
					}
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraints ExactlyK and Exactly1
		// ************************************************************************

		/**
		 * Exactly k variables of the scope, where k is a constant, must be assigned to the specified value.
		 * 
		 */
		public static class ExactlyK extends CountCst implements TagSymmetric, TagCallCompleteFiltering {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Kit.countIn(value, t) == k;
			}

			public ExactlyK(Problem pb, Variable[] list, int value, int k) {
				super(pb, list, value, k);
			}

			@Override
			public boolean runPropagator(Variable x) {
//				if (x.dom.size() > 1 && x.dom.containsValue(value))
//					// removing these two lines, and adding TagCallCompleteFiltering is an alternative
//					return true;

				// nGuaranteedOccurrences denotes the number of singleton domains with the specified value
				// nPossibleOccurrences denotes the number of domains containing the specified value
				int nGuaranteedOccurrences = 0, nPossibleOccurrences = 0;
				for (Variable y : scp)
					if (y.dom.containsValue(value)) {
						nPossibleOccurrences++;
						if (y.dom.size() == 1 && ++nGuaranteedOccurrences > k)
							return y.dom.fail();
					}
				if (nGuaranteedOccurrences == k) {
					int toremove = nPossibleOccurrences - k;
					// remove value from all non singleton domains
					for (int i = futvars.limit; i >= 0 && toremove > 0; i--) {
						Domain dom = scp[futvars.dense[i]].dom;
						if (dom.size() > 1 && dom.containsValue(value)) {
							dom.removeValue(value); // no inconsistency possible
							toremove--;
						}
					}
					return entail();
				}
				if (nPossibleOccurrences < k)
					return x.dom.fail(); // inconsistency detected
				if (nPossibleOccurrences == k) {
					int toassign = k - nGuaranteedOccurrences;
					// assign all non singleton domains containing the value
					for (int i = futvars.limit; i >= 0 && toassign > 0; i--) {
						Domain dom = scp[futvars.dense[i]].dom;
						if (dom.size() > 1 && dom.containsValue(value)) {
							dom.reduceToValue(value);
							toassign--;
						}
					}
					return entail();
				}
				return true;
			}
		}

		public static final class Exactly1 extends ExactlyK {

			public Exactly1(Problem pb, Variable[] list, int value) {
				super(pb, list, value, 1);
			}
		}

	}

	/**********************************************************************************************
	 * CountVar
	 *********************************************************************************************/

	/**
	 * Constraints Count where the right-hand operand (of the condition that must be respected) is a variable
	 */
	public static abstract class CountVar extends Count {

		public static CountVar buildFrom(Problem pb, Variable[] scp, int value, TypeConditionOperatorRel op, Variable k) {
			switch (op) {
			case EQ:
				return new ExactlyVarK(pb, scp, value, k);
			default:
				throw new AssertionError("not implemented");
			}
		}

		/**
		 * The right-operand used in the comparison (i.e., the number of occurrences used as a limit).
		 */
		protected final Variable k;

		/**
		 * The index of the variable in the list if present, -1 otherwise
		 */
		protected final int indexOfKInList;

		/**
		 * Builds a constraint Count for the specified problem, with a limit (k) defined by a variable
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list
		 *            the list where counting is done
		 * @param value
		 *            the value whose number of occurrences must be counted
		 * @param k
		 *            the limit used for comparison in the right-operand
		 */
		public CountVar(Problem pb, Variable[] list, int value, Variable k) {
			super(pb, pb.vars(list, k), list, value);
			this.k = k;
			this.indexOfKInList = Utilities.indexOf(k, list);
			defineKey(value, indexOfKInList);
			// checking the domain of k ?
		}

		/**
		 * Exactly k variables of the specified vector of variables, where k is a variable, must be assigned to the
		 * specified value
		 */
		public final static class ExactlyVarK extends CountVar implements TagCallCompleteFiltering {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				if (indexOfKInList != -1)
					return Kit.countIn(value, t) == t[indexOfKInList];
				int cnt = 0;
				for (int i = 0; i < t.length - 1; i++)
					if (t[i] == value)
						cnt++;
				return cnt == t[t.length - 1];
			}

			public ExactlyVarK(Problem pb, Variable[] list, int value, Variable k) {
				super(pb, list, value, k);
				control(list.length > 1, "list: " + Kit.join(list) + " value: " + value + " k:" + k);
			}

			@Override
			public int[] symmetryMatching() {
				return IntStream.range(0, scp.length).map(i -> i == indexOfKInList || (indexOfKInList == -1 && i == scp.length - 1) ? 2 : 1).toArray();
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// counting the number of occurrences of value in list
				int nGuaranteedOccurrences = 0, nPossibleOccurrences = 0;
				for (Variable x : list)
					if (x.dom.containsValue(value)) {
						nPossibleOccurrences++;
						if (x.dom.size() == 1)
							nGuaranteedOccurrences++;
					}
				Domain dk = k.dom;
				if (dk.size() == 1) {
					int vk = dk.singleValue();
					if (vk < nGuaranteedOccurrences || vk > nPossibleOccurrences)
						return dk.fail();
				} else {
					// possible update of the domain of k when present in the vector, first by removing value (if
					// present) so as to update immediately nPossibleOccurrences
					if (indexOfKInList != -1) {
						int a = dk.toIdxIfPresent(value);
						if (a != -1) {
							boolean deleted = false;
							for (int b = dk.first(); b != -1; b = dk.next(b))
								if (b == a) {
									if (value < nGuaranteedOccurrences + 1 || nPossibleOccurrences < value) {
										// +1 by assuming we assign the value
										if (dk.remove(a) == false)
											return false;
										deleted = true;
									}
								} else {
									int vb = dk.toVal(b);
									if (vb < nGuaranteedOccurrences || nPossibleOccurrences - 1 < vb) {
										// -1 by assuming we assign vb (and not value)
										if (dk.remove(b) == false)
											return false;
									}
								}
							if (deleted)
								nPossibleOccurrences--;
						} else {
							if (dk.removeValuesLT(nGuaranteedOccurrences) == false || dk.removeValuesGT(nPossibleOccurrences) == false)
								return false;
						}
					} else if (dk.removeValuesLT(nGuaranteedOccurrences) == false || dk.removeValuesGT(nPossibleOccurrences) == false)
						return false;
				}
				// if k is singleton, possibly updating the domain of the other variables
				if (dk.size() == 1) {
					int vk = dk.singleValue();
					if (vk == nGuaranteedOccurrences) {
						int toremove = nPossibleOccurrences - vk;
						// remove value from all non singleton domains
						for (int i = futvars.limit; toremove > 0 && i >= 0; i--) {
							Domain dom = scp[futvars.dense[i]].dom;
							if (dom.size() > 1 && dom.containsValue(value)) {
								dom.removeValue(value); // no inconsistency possible
								toremove--;
							}
						}
						return entail();
					}
					if (vk == nPossibleOccurrences) {
						int toassign = vk - nGuaranteedOccurrences;
						// // assign all non singleton domains containing the value
						for (int i = futvars.limit; toassign > 0 && i >= 0; i--) {
							Domain dom = scp[futvars.dense[i]].dom;
							if (dom.size() > 1 && dom.containsValue(value)) {
								dom.reduceToValue(value); // no inconsistency possible
								toassign--;
							}
						}
						return entail();
					}
				}
				return true;
			}
		}
	}

}
