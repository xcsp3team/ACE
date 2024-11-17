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

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import propagation.AC;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * The constraint Element ensures that the value taken by the variable in a list (vector) of variables at a specified index (given by a variable) is equal to a
 * specified value (given by a constant or a variable). The matrix variant involves a matrix of variables and two indices.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Element extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering, TagNotSymmetric {

	/**
	 * Builds a constraint Element for the specified problem and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public Element(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	/**********************************************************************************************
	 * Member
	 *********************************************************************************************/

	public final static class Member extends Element {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			boolean found = false;
			for (int i = 0; !found && i < list.length; i++)
				if (t[i] == value)
					found = true;
			return found == (t[t.length - 1] == 1);
		}

		private final Variable[] list;

		private int value;

		private Variable y;

		/**
		 * Builds a constraint Element for the specified problem, with the specified arguments: list, value and 0/1 variable (y)
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list
		 *            the list (vector) of variables
		 * @param value
		 *            the value whose membership is sought
		 * @param y
		 *            the 0/1 variable indicating if the value is present
		 */
		public Member(Problem pb, Variable[] list, int value, Variable y) {
			super(pb, Utilities.collect(Variable.class, list, y));
			this.list = list;
			this.value = value;
			this.y = y;
			control(list.length >= 2 && Variable.areAllDistinct(list) && y.dom.is01() && Stream.of(list).allMatch(x -> x != y));
			control(scp[scp.length - 1] == y);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (y.dom.size() == 1) {
				if (y.dom.single() == 0) { // y = 0
					for (Variable x : list)
						if (x.dom.removeValueIfPresent(value) == false)
							return false;
					return entailed();
				} else { // y = 1
					int uniqueSentinel = -1;
					for (int i = 0; i < list.length; i++) {
						Domain dom = list[i].dom;
						if (dom.size() == 1) {
							if (dom.singleValue() == value)
								return entailed();
						} else {
							if (dom.containsValue(value)) {
								if (uniqueSentinel == -1)
									uniqueSentinel = i;
								else
									return true; // because two sentinels
							}
						}
					}
					if (uniqueSentinel == -1)
						return y.dom.fail();
					return list[uniqueSentinel].dom.reduceToValue(value) && entailed();
				}
			}
			assert y.dom.size() == 2;
			boolean found = false;
			for (Variable x : list) {
				if (x.dom.size() == 1) {
					if (x.dom.singleValue() == value)
						return y.dom.remove(0) && entailed(); // no possible inconsistency here
				} else {
					if (x.dom.containsValue(value))
						found = true;
				}
			}
			if (!found)
				return y.dom.remove(1) && entailed(); // no possible inconsistency here
			return true;
		}
	}

	/**********************************************************************************************
	 * ElementList, with its two subclasses ElementCst and ElementVar
	 *********************************************************************************************/

	/**
	 * The root class of Element constraints based on a list (vector) of variables
	 */
	public abstract static class ElementList extends Element {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			throw new AssertionError("Actually, we reason with checkIndexes. This is less expensive (no need to convert all values)");
		}

		/**
		 * The list (vector) of variables
		 */
		protected final Variable[] list;

		/**
		 * The domain of the index variable
		 */
		protected final Domain idom;

		/**
		 * The position of the index variable in the constraint scope
		 */
		protected final int ipos;

		/**
		 * Builds a constraint Element for the specified problem, with the specified arguments: list, index and value
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list
		 *            the list (vector) of variables
		 * @param index
		 *            the variable used as index
		 * @param value
		 *            the object (integer constant or variable) used as target value
		 */
		public ElementList(Problem pb, Variable[] list, Variable index, Object value) {
			super(pb, Utilities.collect(Variable.class, list, index, value));
			this.list = list;
			this.idom = index.dom;
			this.ipos = IntStream.range(0, scp.length).filter(i -> scp[i] == index).findFirst().getAsInt();
			control(Variable.areAllDistinct(list) && index != value, () -> "i=" + index + " x=" + Kit.join(list) + " v=" + value);
			control(list.length == idom.initSize(), " pb with " + this + " " + index);
			// the last control above because we reason with indexes (and not values) for idom
			// for example if idom={2,3,5}, we have list.length=3 and we refer to variables of list with indexes 0, 1
			// and 2 ; this is enforced at construction (in Problem)
		}

		// ************************************************************************
		// ***** Constraint ElementCst
		// ************************************************************************

		/**
		 * The constraint Element with an integer constant used as target value
		 */
		public final static class ElementCst extends ElementList {

			@Override
			public boolean checkIndexes(int[] t) {
				return list[t[ipos]].dom.toVal(t[t[ipos]]) == k;
			}

			/**
			 * The integer constant used as target value
			 */
			private final int k;

			public ElementCst(Problem pb, Variable[] list, Variable index, int value) {
				super(pb, list, index, value);
				this.k = value;
				// some values may be deleted at construction time
				idom.removeAtConstructionTime(a -> !list[a].dom.containsValue(k));
				if (ipos < list.length && idom.toVal(ipos) != k) // special case (index in list)
					idom.removeValueAtConstructionTime(k); // equivalent to idom.removeAtConstructionTime(ipos). right?
				defineKey(value);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (idom.size() > 1) {
					// checking that the values of index are still valid
					int sizeBefore = idom.size();
					for (int a = idom.first(); a != -1; a = idom.next(a))
						if (!list[a].dom.containsValue(k))
							idom.removeElementary(a);
					if (idom.afterElementaryCalls(sizeBefore) == false)
						return false;
				}
				// be careful : not a else because of statements above that may modify the domain of index
				if (idom.size() > 1)
					return true;
				return list[idom.single()].dom.reduceToValue(k) && entailed();
			}
		}

		// ************************************************************************
		// ***** Constraint ElementVar
		// ************************************************************************

		/**
		 * The constraint Element with an integer variable used as target value
		 */
		public final static class ElementVar extends ElementList {

			@Override
			public boolean checkIndexes(int[] t) {
				return list[t[ipos]].dom.toVal(t[t[ipos]]) == vdom.toVal(t[vpos]);
			}

			/**
			 * The domain of the value variable
			 */
			private final Domain vdom;

			/**
			 * The position of the value variable in the constraint scope
			 */
			private final int vpos;

			/**
			 * indexSentinels[i] stores, for the ith variable of the list (vector), a value that is both in its domain and in vdom
			 */
			private final int[] indexSentinels;

			/**
			 * valueSentinels[a] stores, for each index a of a value v in vdom, the index i of a variable in list such that v is in the domain of this variable
			 */
			private final int[] valueSentinels;

			public ElementVar(Problem pb, Variable[] list, Variable index, Variable value) {
				super(pb, list, index, value);
				this.vdom = value.dom;
				this.vpos = IntStream.range(0, scp.length).filter(i -> scp[i] == value).findFirst().getAsInt();
				this.valueSentinels = Kit.repeat(-1, value.dom.initSize());
				this.indexSentinels = Kit.repeat(Integer.MIN_VALUE, list.length);
				// TODO control that each value in vdom is in at least one domain of the list?
			}

			private boolean validIndex(int i) {
				int v = indexSentinels[i];
				if (v != Integer.MIN_VALUE && list[i].dom.containsValue(v) && vdom.containsValue(v))
					return true;
				Domain dom = list[i].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					v = dom.toVal(a);
					if (vdom.containsValue(v)) {
						indexSentinels[i] = v;
						return true;
					}
				}
				return false;
			}

			private boolean filterIndex() {
				return idom.removeIndexesChecking(i -> !validIndex(i));
			}

			private boolean validValue(int a) {
				int v = vdom.toVal(a);
				int sentinel = valueSentinels[a];
				if (sentinel != -1 && idom.contains(sentinel) && list[sentinel].dom.containsValue(v))
					return true;
				for (int i = idom.first(); i != -1; i = idom.next(i)) {
					if (list[i].dom.containsValue(v)) {
						valueSentinels[a] = i;
						return true;
					}
				}
				return false;
			}

			private boolean filterValue() {
				return vdom.removeIndexesChecking(a -> !validValue(a));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// If idom is not singleton, we try to prune values :
				// - in vdom, we prune the values which are not in any domain of the list variables
				// - in idom, we prune the values i for which there is no v such that list[i].dom and vdom
				// both contain v
				if (idom.size() > 1) {
					// updating vdom (and valueSentinels)
					if (filterValue() == false)
						return false;
					while (true) {
						// updating idom (and indexSentinels)
						int sizeBefore = idom.size();
						if (filterIndex() == false)
							return false;
						if (sizeBefore == idom.size())
							break;
						// updating vdom (and valueSentinels)
						sizeBefore = vdom.size();
						if (filterValue() == false)
							return false;
						if (sizeBefore == vdom.size())
							break;
					}
				}
				// If index is singleton, we update dom(list[index]) and vdom so that they are both equal to the
				// intersection of the two domains
				if (idom.size() == 1) {
					if (AC.enforceEQ(list[idom.single()].dom, vdom) == false)
						return false;
					if (vdom.size() == 1)
						return entailed();
				}
				return true;
			}

			@Override
			public boolean controlAC() {
				control(idom.size() != 1 || list[idom.single()].dom.subsetOf(vdom), () -> "index is singleton and dom(index) is not included in dom(result).");
				for (int a = idom.first(); a != -1; a = idom.next(a))
					control(list[a].dom.overlapWith(vdom), () -> "One var has no value in dom(result).");
				extern: for (int a = vdom.first(); a != -1; a = vdom.next(a)) {
					int v = vdom.toVal(a);
					for (int b = idom.first(); b != -1; b = idom.next(b))
						if (list[b].dom.containsValue(v))
							continue extern;
					idom.display(1);
					if (idom.size() == 1)
						list[idom.singleValue()].display(2);
					vdom.display(2);
					control(false, () -> "pb in " + this + ": value " + v + " is in dom(value) but in no list variable whose index is still in dom(index).");
				}
				return true;
			}
		}
	}

	/**********************************************************************************************
	 * ElementMatrix, with its two subclasses ElementMatrixCst and ElementMatrixVar
	 *********************************************************************************************/

	/**
	 * The root class of Element constraints based on a matrix of variables
	 */
	public abstract static class ElementMatrix extends Element {

		/**
		 * The matrix of variables
		 */
		protected final Variable[][] matrix;

		/**
		 * The domain of the row index variable
		 */
		protected final Domain rdom;

		/**
		 * The domain of the column index variable
		 */
		protected final Domain cdom;

		/**
		 * The position of the row index variable in the constraint scope
		 */
		protected final int rpos;

		/**
		 * The position of the column index variable in the constraint scope
		 */
		protected final int cpos;

		public ElementMatrix(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, Object value) {
			super(pb, Utilities.collect(Variable.class, matrix, rindex, cindex, value)); // value may be a variable
			this.matrix = matrix;
			this.rdom = rindex.dom;
			this.cdom = cindex.dom;
			this.rpos = IntStream.range(0, scp.length).filter(i -> scp[i] == rindex).findFirst().getAsInt();
			this.cpos = IntStream.range(0, scp.length).filter(i -> scp[i] == cindex).findFirst().getAsInt();
			int n = matrix.length, m = matrix[0].length;
			control(Variable.areAllDistinct(pb.vars(matrix)) && rindex != cindex, () -> Kit.join(matrix) + " " + rindex + " " + cindex);
			rdom.removeValuesAtConstructionTime(v -> v < 0 || v >= n);
			cdom.removeValuesAtConstructionTime(v -> v < 0 || v >= m);
		}

		// ************************************************************************
		// ***** Constraint ElementMatrixCst
		// ************************************************************************

		/**
		 * The matrix variant of the constraint Element with an integer constant used as target value
		 */
		public final static class ElementMatrixCst extends ElementMatrix {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				int i = t[rpos], j = t[cpos];
				return t[i * matrix[0].length + j] == k;
			}

			/**
			 * The integer constant used as target value
			 */
			private final int k;

			private final int[] rsentinels, csentinels;

			public ElementMatrixCst(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, int value) {
				super(pb, matrix, rindex, cindex, value);
				this.k = value;
				defineKey(value);
				int n = matrix.length, m = matrix[0].length;
				this.rsentinels = new int[n];
				this.csentinels = new int[m];
				// defineKey(value);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// filtering rdom
				int sizeBefore = rdom.size();
				if (sizeBefore > 1) {
					extern: for (int a = rdom.last(); a != -1; a = rdom.prev(a)) {
						int b = rsentinels[a];
						if (cdom.contains(b) && matrix[rdom.toVal(a)][cdom.toVal(b)].dom.containsValue(k))
							continue;
						for (b = cdom.last(); b != -1; b = cdom.prev(b))
							if (matrix[rdom.toVal(a)][cdom.toVal(b)].dom.containsValue(k)) {
								rsentinels[a] = b;
								continue extern;
							}
						rdom.removeElementary(a);
					}
					if (rdom.afterElementaryCalls(sizeBefore) == false)
						return false;
				}

				// filtering cdom
				sizeBefore = cdom.size();
				if (sizeBefore > 1) {
					extern: for (int b = cdom.last(); b != -1; b = cdom.prev(b)) {
						int a = csentinels[b];
						if (rdom.contains(a) && matrix[rdom.toVal(a)][cdom.toVal(b)].dom.containsValue(k))
							continue;
						for (a = rdom.last(); a != -1; a = rdom.prev(a)) {
							if (matrix[rdom.toVal(a)][cdom.toVal(b)].dom.containsValue(k)) {
								csentinels[b] = a;
								continue extern;
							}
						}
						cdom.removeElementary(b);
					}
					if (cdom.afterElementaryCalls(sizeBefore) == false)
						return false;
				}
				// be careful : below, not a else because of statements above that may modify the domain of indexes
				// TODO are we sure it is AC?
				return rdom.size() > 1 || cdom.size() > 1 || (matrix[rdom.singleValue()][cdom.singleValue()].dom.reduceToValue(k) && entailed());
			}
		}

		// ************************************************************************
		// ***** Constraint ElementMatrixVar
		// ************************************************************************

		/**
		 * The matrix variant of the constraint Element with an integer variable used as target value
		 */
		public final static class ElementMatrixVar extends ElementMatrix {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				int i = t[rpos], j = t[cpos];
				return t[i * matrix[0].length + j] == t[vpos];
			}

			/**
			 * The domain of the value variable
			 */
			private final Domain vdom;

			/**
			 * The position of the value variable in the constraint scope
			 */
			private final int vpos;

			private final int[] rindexColSentinels, rindexValSentinels;
			private final int[] cindexRowSentinels, cindexValSentinels;
			private final int[] valueRowSentinels, valueColSentinels;

			public ElementMatrixVar(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, Variable value) {
				super(pb, matrix, rindex, cindex, value);
				this.vdom = value.dom;
				this.vpos = IntStream.range(0, scp.length).filter(i -> scp[i] == value).findFirst().getAsInt();
				int n = matrix.length, m = matrix[0].length, d = value.dom.initSize();
				this.rindexColSentinels = Kit.repeat(-1, n);
				this.rindexValSentinels = Kit.repeat(-1, n);
				this.cindexRowSentinels = Kit.repeat(-1, m);
				this.cindexValSentinels = Kit.repeat(-1, m);
				this.valueRowSentinels = Kit.repeat(-1, d);
				this.valueColSentinels = Kit.repeat(-1, d);
			}

			private boolean validRowIndex(int i) {
				int j = rindexColSentinels[i], v = rindexValSentinels[i];
				if (j != -1 && cdom.contains(j) && matrix[rdom.toVal(i)][cdom.toVal(j)].dom.containsValue(v) && vdom.containsValue(v))
					return true;
				for (j = cdom.first(); j != -1; j = cdom.next(j)) {
					Domain dom = matrix[rdom.toVal(i)][cdom.toVal(j)].dom;
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int va = dom.toVal(a);
						if (vdom.containsValue(va)) {
							rindexColSentinels[i] = j;
							rindexValSentinels[i] = va;
							return true;
						}
					}
				}
				return false;
			}

			private boolean validColIndex(int j) {
				int i = cindexRowSentinels[j], v = cindexValSentinels[j];
				if (i != -1 && rdom.contains(i) && matrix[rdom.toVal(i)][cdom.toVal(j)].dom.containsValue(v) && vdom.containsValue(v))
					return true;
				for (i = rdom.first(); i != -1; i = rdom.next(i)) {
					Domain dom = matrix[rdom.toVal(i)][cdom.toVal(j)].dom;
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int va = dom.toVal(a);
						if (vdom.containsValue(va)) {
							cindexRowSentinels[j] = i;
							cindexValSentinels[j] = va;
							return true;
						}
					}
				}
				return false;
			}

			private boolean filterIndex() {
				return rdom.removeIndexesChecking(i -> !validRowIndex(i)) && cdom.removeIndexesChecking(j -> !validColIndex(j));
			}

			private boolean validValue(int a) {
				int va = vdom.toVal(a);
				int i = valueRowSentinels[a], j = valueColSentinels[a];
				if (i != -1 && rdom.contains(i) && cdom.contains(j) && matrix[rdom.toVal(i)][cdom.toVal(j)].dom.containsValue(va))
					return true;
				for (i = rdom.first(); i != -1; i = rdom.next(i))
					for (j = cdom.first(); j != -1; j = cdom.next(j)) {
						if (matrix[rdom.toVal(i)][cdom.toVal(j)].dom.containsValue(va)) {
							valueRowSentinels[a] = i;
							valueColSentinels[a] = j;
							return true;
						}
					}
				return false;
			}

			private boolean filterValue() {
				return vdom.removeIndexesChecking(a -> !validValue(a));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// If indexes are not both singleton, we try to prune values :
				// - in vdom, we prune the values which are not in any of the domains of the list variables
				// - in rdom and cdom, we prune the values that cannot lead to any value in vdom
				if (rdom.size() > 1 || cdom.size() > 1) {
					// updating vdom (and some sentinels)
					if (filterValue() == false)
						return false;
					while (true) {
						// updating rdom,and cdom (and some sentinels)
						int sizeBefore = rdom.size() + cdom.size();
						if (filterIndex() == false)
							return false;
						if (sizeBefore == rdom.size() + cdom.size())
							break;
						// updating vdom (and some sentinels)
						sizeBefore = vdom.size();
						if (filterValue() == false)
							return false;
						if (sizeBefore == vdom.size())
							break;
					}
				}
				// If indexes are both singleton, we enforce value to the corresponding cell of the matrix
				if (rdom.size() == 1 && cdom.size() == 1) {
					if (AC.enforceEQ(matrix[rdom.singleValue()][cdom.singleValue()].dom, vdom) == false)
						return false;
					if (vdom.size() == 1)
						return entailed();
				}
				return true;
			}
		}
	}
}
