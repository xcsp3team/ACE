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

	protected final Variable[] list;

	protected final Domain idom; // domain of the index variable
	protected final int ipos; // position in scope of the index variable

	public Element(Problem pb, Variable[] list, int startAt, Variable index, Object value) {
		super(pb, Utilities.collect(Variable.class, list, index, value)); // value may be a variable
		this.list = list;
		this.idom = index.dom;
		this.ipos = IntStream.range(0, scp.length).filter(i -> scp[i] == index).findFirst().getAsInt();
		control(startAt == 0, "Starting at a value different from 0 not implemented");
		control(Variable.areAllDistinct(list) && index != value, "i=" + index + " x=" + Kit.join(list) + " v=" + value);
		idom.removeValuesAtConstructionTime(v -> v < 0 || v >= list.length);
	}

	@Override
	public boolean checkValues(int[] t) { // reasoning from checkIndexes is less expensive (no need to convert all values)
		throw new AssertionError();
	}

	// ************************************************************************
	// ***** Constraint ElementConstant
	// ************************************************************************

	public final static class ElementCst extends Element {
		private final int k;

		public boolean checkIndexes(int[] t) {
			int idx = idom.toVal(t[ipos]);
			return list[idx].dom.toVal(t[idx]) == k;
		}

		public ElementCst(Problem pb, Variable[] list, int startAt, Variable index, int value) {
			super(pb, list, startAt, index, value);
			this.k = value;
			defineKey(value, startAt);
			control(Variable.areAllDomainsContainingValue(list, k));
			if (ipos < list.length && list[ipos].dom.toVal(ipos) != k) // special case (index in list)
				idom.removeValueAtConstructionTime(k);
		}

		public ElementCst(Problem pb, Variable[] list, Variable index, int value) {
			this(pb, list, 0, index, value);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (idom.size() > 1) { // checking that the values of index are still valid
				int sizeBefore = idom.size();
				for (int a = idom.first(); a != -1; a = idom.next(a))
					if (!list[idom.toVal(a)].dom.presentValue(k))
						idom.removeElementary(a);
				if (idom.afterElementaryCalls(sizeBefore) == false)
					return false;
			}
			// be careful : not a else because of statements above that may modify the domain of index
			if (idom.size() > 1)
				return true;
			return list[idom.uniqueValue()].dom.reduceToValue(k) && entailed();
		}
	}

	// ************************************************************************
	// ***** Constraint ElementVariable
	// ************************************************************************

	/**
	 * Such a constraint is satisfied iff list[index] = value
	 */
	public final static class ElementVar extends Element {

		private final Domain vdom; // domain of the value variable
		private final int vpos; // position of the value variable in scope

		public boolean checkIndexes(int[] t) {
			int idx = idom.toVal(t[ipos]);
			return list[idx].dom.toVal(t[idx]) == vdom.toVal(t[vpos]);
			// int i = t[ipos];
			// return list[i].dom.toVal(t[i]) == vdom.toVal(t[vpos]);
		}

		/**
		 * For each variable in list, we store a (normalized) value that is both in its domain and in value's domain
		 */
		private final int[] indexSentinels;

		/**
		 * For each (index of a) value v in value's domain, we store the index i of a variable from list such that v is in dom(list[i]).
		 */
		private final int[] valueSentinels;

		public ElementVar(Problem pb, Variable[] list, int startAt, Variable index, Variable value) {
			super(pb, list, startAt, index, value);
			this.vdom = value.dom;
			this.vpos = IntStream.range(0, scp.length).filter(i -> scp[i] == value).findFirst().getAsInt();
			this.valueSentinels = Kit.repeat(-1, value.dom.initSize());
			this.indexSentinels = Kit.repeat(-1, list.length);
			defineKey();
			// TODO control that each value in vdom is in at least one domain of the list?
		}

		public ElementVar(Problem pb, Variable[] list, Variable index, Variable value) {
			this(pb, list, 0, index, value);
		}

		private boolean validIndex(int i) {
			Domain dom = list[idom.toVal(i)].dom;
			int v = indexSentinels[i];
			if (v != -1 && dom.presentValue(v) && vdom.presentValue(v))
				return true;
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
			int i = valueSentinels[a];
			if (i != -1 && idom.present(i) && list[idom.toVal(i)].dom.presentValue(va))
				return true;
			for (i = idom.first(); i != -1; i = idom.next(i)) {
				if (list[idom.toVal(i)].dom.presentValue(va)) {
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
				if (PrimitiveBinary.enforceEQ(list[idom.uniqueValue()].dom, vdom) == false)
					return false;
				if (vdom.size() == 1)
					return entailed();
			}
			return true;
		}

		private boolean controlAC() {
			control(idom.size() != 1 || list[idom.uniqueValue()].dom.subsetOf(vdom), () -> "index is singleton and dom(index) is not included in dom(result).");
			for (int a = idom.first(); a != -1; a = idom.next(a))
				control(list[idom.toVal(a)].dom.overlapWith(vdom), () -> "One var has no value in dom(result).");
			extern: for (int a = vdom.first(); a != -1; a = vdom.next(a)) {
				int v = vdom.toVal(a);
				for (int b = idom.first(); b != -1; b = idom.next(b))
					if (list[idom.toVal(b)].dom.presentValue(v))
						continue extern;
				control(false, () -> "value " + v + " is in dom(value) but in no list variable whose index is still in dom(index).");
			}
			return true;
		}

	}
}
