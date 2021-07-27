/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.Constraint.CtrGlobal;
import constraints.intension.PrimitiveBinary;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class Element extends CtrGlobal implements TagNotSymmetric, TagAC, TagFilteringCompleteAtEachCall {

	public Element(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	/**********************************************************************************************
	 * ElementArray
	 *********************************************************************************************/

	public abstract static class ElementArray extends Element {

		protected final Variable[] list;

		protected final Domain idom; // domain of the index variable
		protected final int ipos; // position in scope of the index variable

		public ElementArray(Problem pb, Variable[] list, Variable index, Object value) {
			super(pb, Utilities.collect(Variable.class, list, index, value)); // value may be a variable
			this.list = list;
			this.idom = index.dom;
			this.ipos = IntStream.range(0, scp.length).filter(i -> scp[i] == index).findFirst().getAsInt();
			control(Variable.areAllDistinct(list) && index != value, "i=" + index + " x=" + Kit.join(list) + " v=" + value);
			control(list.length == idom.initSize(), " pb with " + this + " " + index);
			// control above because we reason with indexes (and not values) for idom
			// for example if idom={2,3,5}, we have list.length=3 and we refer to variables of list with indexes 0, 1 and 2
			// this is enforced at construction (in problem)
		}

		@Override
		public boolean checkValues(int[] t) { // reasoning from checkIndexes is less expensive (no need to convert all values)
			throw new AssertionError();
		}
	}

	// ************************************************************************
	// ***** Constraint ElementCst
	// ************************************************************************

	public final static class ElementCst extends ElementArray {
		private final int k;

		public boolean checkIndexes(int[] t) {
			return list[t[ipos]].dom.toVal(t[t[ipos]]) == k;
		}

		public ElementCst(Problem pb, Variable[] list, Variable index, int value) {
			super(pb, list, index, value);
			this.k = value;
			defineKey(value);
			idom.removeAtConstructionTime(a -> !list[a].dom.presentValue(k));
			if (ipos < list.length && idom.toVal(ipos) != k) // special case (index in list)
				idom.removeValueAtConstructionTime(k); // equivalent to idom.removeAtConstructionTime(ipos). right?
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (idom.size() > 1) { // checking that the values of index are still valid
				int sizeBefore = idom.size();
				for (int a = idom.first(); a != -1; a = idom.next(a))
					if (!list[a].dom.presentValue(k))
						idom.removeElementary(a);
				if (idom.afterElementaryCalls(sizeBefore) == false)
					return false;
			}
			// be careful : not a else because of statements above that may modify the domain of index
			if (idom.size() > 1)
				return true;
			return list[idom.unique()].dom.reduceToValue(k) && entailed();
		}
	}

	// ************************************************************************
	// ***** Constraint ElementVar
	// ************************************************************************

	/**
	 * Such a constraint is satisfied iff list[index] = value
	 */
	public final static class ElementVar extends ElementArray {

		private final Domain vdom; // domain of the value variable
		private final int vpos; // position of the value variable in scope

		public boolean checkIndexes(int[] t) {
			return list[t[ipos]].dom.toVal(t[t[ipos]]) == vdom.toVal(t[vpos]);
		}

		/**
		 * For each variable in list, we store a (normalized) value that is both in its domain and in value's domain
		 */
		private final int[] indexSentinels;

		/**
		 * For each (index of a) value v in value's domain, we store the index i of a variable from list such that v is in dom(list[i]).
		 */
		private final int[] valueSentinels;

		public ElementVar(Problem pb, Variable[] list, Variable index, Variable value) {
			super(pb, list, index, value);
			this.vdom = value.dom;
			this.vpos = IntStream.range(0, scp.length).filter(i -> scp[i] == value).findFirst().getAsInt();
			this.valueSentinels = Kit.repeat(-1, value.dom.initSize());
			this.indexSentinels = Kit.repeat(-1, list.length);
			defineKey();
			// TODO control that each value in vdom is in at least one domain of the list?
		}

		private boolean validIndex(int i) {
			int v = indexSentinels[i];
			if (v != -1 && list[i].dom.presentValue(v) && vdom.presentValue(v))
				return true;
			Domain dom = list[i].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int va = dom.toVal(a);
				if (vdom.presentValue(va)) {
					indexSentinels[i] = va;
					return true;
				}
			}
			return false;
		}

		private boolean filterIndex() {
			return idom.removeIndexesChecking(i -> !validIndex(i));
		}

		private boolean validValue(int a) {
			int va = vdom.toVal(a);
			int sentinel = valueSentinels[a];
			if (sentinel != -1 && idom.present(sentinel) && list[sentinel].dom.presentValue(va))
				return true;
			for (int i = idom.first(); i != -1; i = idom.next(i)) {
				if (list[i].dom.presentValue(va)) {
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
			// If index is not singleton, we try to prune values :
			// - in value's domain, we prune the values which aren't in any of list variables'domains
			// - in index's domain, we prune the values v for which there is no value j such that list[v] and value both have j in their
			// domains
			if (idom.size() > 1) {
				// Update valueSentinels and domain of the value variable
				if (filterValue() == false)
					return false;
				while (true) {
					// Update listSentinels and domain of the index variable
					int sizeBefore = idom.size();
					if (filterIndex() == false)
						return false;
					if (sizeBefore == idom.size())
						break;
					// Update valueSentinels and domain of the value variable
					sizeBefore = vdom.size();
					if (filterValue() == false)
						return false;
					if (sizeBefore == vdom.size())
						break;
				}
			}
			// If index is singleton, we update dom(list[index]) and dom(value) so that they are both equal to the intersection of the two domains
			if (idom.size() == 1) {
				if (PrimitiveBinary.enforceEQ(list[idom.unique()].dom, vdom) == false)
					return false;
				if (vdom.size() == 1)
					return entailed();
			}
			return true;
		}

		private boolean controlAC() {
			control(idom.size() != 1 || list[idom.unique()].dom.subsetOf(vdom), () -> "index is singleton and dom(index) is not included in dom(result).");
			for (int a = idom.first(); a != -1; a = idom.next(a))
				control(list[a].dom.overlapWith(vdom), () -> "One var has no value in dom(result).");
			extern: for (int a = vdom.first(); a != -1; a = vdom.next(a)) {
				int v = vdom.toVal(a);
				for (int b = idom.first(); b != -1; b = idom.next(b))
					if (list[b].dom.presentValue(v))
						continue extern;
				control(false, () -> "value " + v + " is in dom(value) but in no list variable whose index is still in dom(index).");
			}
			return true;
		}
	}

	/**********************************************************************************************
	 * ElementMatrix
	 *********************************************************************************************/

	public abstract static class ElementMatrix extends Element {

		protected Variable[][] matrix;

		protected Domain rdom, cdom;
		protected int rindexPosition, cindexPosition; // in scope

		public ElementMatrix(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, Object value) {
			super(pb, Utilities.collect(Variable.class, matrix, rindex, cindex, value)); // value may be a variable
			this.matrix = matrix;
			this.rdom = rindex.dom;
			this.cdom = cindex.dom;
			this.rindexPosition = IntStream.range(0, scp.length).filter(i -> scp[i] == rindex).findFirst().getAsInt();
			this.cindexPosition = IntStream.range(0, scp.length).filter(i -> scp[i] == cindex).findFirst().getAsInt();
			int n = matrix.length, m = matrix[0].length;
			control(Variable.areAllDistinct(pb.vars(matrix)) && rindex != cindex, () -> Kit.join(matrix) + " " + rindex + " " + cindex);
			rdom.removeValuesAtConstructionTime(v -> v < 0 || v >= n);
			cdom.removeValuesAtConstructionTime(v -> v < 0 || v >= m);
		}

		// ************************************************************************
		// ***** Constraint ElementMatrixCst
		// ************************************************************************

		public final static class ElementMatrixCst extends ElementMatrix {
			private int value;

			private int[] rsentinels, csentinels;

			@Override
			public boolean checkValues(int[] t) {
				int i = t[rindexPosition], j = t[cindexPosition];
				return t[i * matrix.length + j] == value;
			}

			public ElementMatrixCst(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, int value) {
				super(pb, matrix, rindex, cindex, value);
				this.value = value;
				defineKey(value);
				int n = matrix.length, m = matrix[0].length;
				this.rsentinels = new int[n];
				this.csentinels = new int[m];
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// filtering the domain of rindex
				int sizeBefore = rdom.size();
				if (sizeBefore > 1) {
					extern: for (int a = rdom.last(); a != -1; a = rdom.prev(a)) {
						int b = rsentinels[a];
						if (cdom.present(b) && matrix[rdom.toVal(a)][cdom.toVal(b)].dom.presentValue(value))
							continue;
						for (b = cdom.last(); b != -1; b = cdom.prev(b))
							if (matrix[rdom.toVal(a)][cdom.toVal(b)].dom.presentValue(value)) {
								rsentinels[a] = b;
								continue extern;
							}
						rdom.removeElementary(a);
					}
					if (rdom.afterElementaryCalls(sizeBefore) == false)
						return false;
				}

				// filtering the domain of cindex
				sizeBefore = cdom.size();
				if (sizeBefore > 1) {
					extern: for (int b = cdom.last(); b != -1; b = cdom.prev(b)) {
						int a = csentinels[b];
						if (rdom.present(a) && matrix[rdom.toVal(a)][cdom.toVal(b)].dom.presentValue(value))
							continue;
						for (a = rdom.last(); a != -1; a = rdom.prev(a)) {
							if (matrix[rdom.toVal(a)][cdom.toVal(b)].dom.presentValue(value)) {
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
				// TODO are we sure it is GAC?
				return rdom.size() > 1 || cdom.size() > 1 || (matrix[rdom.uniqueValue()][cdom.uniqueValue()].dom.reduceToValue(value) && entailed());
			}
		}

		// ************************************************************************
		// ***** Constraint ElementMatrixVar
		// ************************************************************************

		public final static class ElementMatrixVar extends ElementMatrix {

			private final Domain vdom; // domain of the value variable
			private final int vpos; // position in scope of the value variable

			private final int[] rindexColSentinels, rindexValSentinels;
			private final int[] cindexRowSentinels, cindexValSentinels;
			private final int[] valueRowSentinels, valueColSentinels;

			@Override
			public boolean checkValues(int[] t) {
				int i = t[rindexPosition], j = t[cindexPosition];
				return t[i * matrix.length + j] == t[vpos];
			}

			public ElementMatrixVar(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, Variable value) {
				super(pb, matrix, rindex, cindex, value);
				defineKey();
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
				if (j != -1 && cdom.present(j) && matrix[rdom.toVal(i)][cdom.toVal(j)].dom.presentValue(v) && vdom.presentValue(v))
					return true;
				for (j = cdom.first(); j != -1; j = cdom.next(j)) {
					Domain dom = matrix[rdom.toVal(i)][cdom.toVal(j)].dom;
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int va = dom.toVal(a);
						if (vdom.presentValue(va)) {
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
				if (i != -1 && rdom.present(i) && matrix[rdom.toVal(i)][cdom.toVal(j)].dom.presentValue(v) && vdom.presentValue(v))
					return true;
				for (i = rdom.first(); i != -1; i = rdom.next(i)) {
					Domain dom = matrix[rdom.toVal(i)][cdom.toVal(j)].dom;
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int va = dom.toVal(a);
						if (vdom.presentValue(va)) {
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
				if (i != -1 && rdom.present(i) && cdom.present(j) && matrix[rdom.toVal(i)][cdom.toVal(j)].dom.presentValue(va))
					return true;
				for (i = rdom.first(); i != -1; i = rdom.next(i))
					for (j = cdom.first(); j != -1; j = cdom.next(j)) {
						if (matrix[rdom.toVal(i)][cdom.toVal(j)].dom.presentValue(va)) {
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
				// - in value's domain, we prune the values which aren't in any of list variables'domains
				// - in indexes's domain, we prune the values v for which there is no value v such that matrix and value both have j in their
				// domains
				if (rdom.size() > 1 || cdom.size() > 1) {
					// Update valueSentinels and domain of the value variable
					if (filterValue() == false)
						return false;
					while (true) {
						// Update listSentinels and domain of the index variable
						int sizeBefore = rdom.size() + cdom.size();
						if (filterIndex() == false)
							return false;
						if (sizeBefore == rdom.size() + cdom.size())
							break;
						// Update valueSentinels and domain of the value variable
						sizeBefore = vdom.size();
						if (filterValue() == false)
							return false;
						if (sizeBefore == vdom.size())
							break;
					}
				}
				// If indexes are both singleton, we enforce matrix[rindex][cindex] == value
				if (rdom.size() == 1 && cdom.size() == 1) {
					if (PrimitiveBinary.enforceEQ(matrix[rdom.uniqueValue()][cdom.uniqueValue()].dom, vdom) == false)
						return false;
					if (vdom.size() == 1)
						return entailed();
				}
				return true;
			}
		}
	}
}
