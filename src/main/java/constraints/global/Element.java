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
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class Element extends CtrGlobal implements TagNotSymmetric, TagAC {

	protected final Variable[] list;

	protected final Variable ivar; // index variable
	protected final Domain idom;
	protected final int ipos; // index variable position in scope

	public Element(Problem pb, Variable[] list, int startAt, Variable index, Object value) {
		super(pb, Utilities.collect(Variable.class, list, index, value)); // value may be a variable
		this.list = list;
		this.ivar = index;
		this.idom = index.dom;
		this.ipos = IntStream.range(0, scp.length).filter(i -> scp[i] == index).findFirst().getAsInt();
		control(startAt == 0, "Starting at a value different from 0 not implemented");
		control(Variable.areAllDistinct(list) && index != value, "i=" + index + " x=" + Kit.join(list) + " v=" + value);
		control(list.length == idom.initSize(), " pb with " + this + " " + index);
	}

	// returns the domain of the variable in list whose position is given by the specified integer (note that startAt is paid attention to)
	protected Domain domAt(int i) {
		return list[i].dom;
	}

	// ************************************************************************
	// ***** Constraint ElementConstant
	// ************************************************************************

	public static class ElementConstant extends Element implements TagFilteringCompleteAtEachCall {
		private final int k;

		@Override
		public boolean checkValues(int[] t) {
			throw new AssertionError();
		}

		public boolean checkIndexes(int[] t) {
			int i = t[ipos];
			return list[i].dom.toVal(t[i]) == k;
		}

		public ElementConstant(Problem pb, Variable[] list, int startAt, Variable index, int value) {
			super(pb, list, startAt, index, value);
			this.k = value;
			defineKey(value, startAt);
			control(Variable.areAllDomainsContainingValue(list, k));
			if (ipos < list.length && list[ipos].dom.toVal(ipos) != k) // special case (index in list)
				idom.removeValueAtConstructionTime(k);
		}

		public ElementConstant(Problem pb, Variable[] list, Variable index, int value) {
			this(pb, list, 0, index, value);
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
	// ***** Constraint ElementVariable
	// ************************************************************************

	/**
	 * Such a constraint is satisfied iff list[index] = value
	 */
	public static class ElementVariable extends Element implements TagFilteringCompleteAtEachCall {

		private final Variable vvar; // value variable
		private final Domain vdom;
		private final int vpos; // value variable position in scope

		@Override
		public boolean checkValues(int[] t) {
			throw new AssertionError();
		}

		public boolean checkIndexes(int[] t) {
			int i = t[ipos];
			return list[i].dom.toVal(t[i]) == vdom.toVal(t[vpos]);
		}

		/**
		 * For each index a of a value v in value's domain, we store the index i of a variable from list such that v is in dom(list[i]).
		 */
		private final int[] valueSentinels;

		/**
		 * For each variable in list, we store a (normalized) value that is both in its domain and in value's domain
		 */
		private final int[] listSentinels;

		public ElementVariable(Problem pb, Variable[] list, int startAt, Variable index, Variable value) {
			super(pb, list, startAt, index, value);
			this.vvar = value;
			this.vdom = value.dom;
			this.vpos = IntStream.range(0, scp.length).filter(i -> scp[i] == value).findFirst().getAsInt();
			this.valueSentinels = Kit.repeat(-1, value.dom.initSize());
			this.listSentinels = Kit.repeat(-1, list.length);
			defineKey();
			// TODO control that each value in vdom is in at least one domain of the list?
		}

		public ElementVariable(Problem pb, Variable[] list, Variable index, Variable value) {
			this(pb, list, 0, index, value);
		}

		private boolean validSentinelForListAt(int i) {
			int sentinel = listSentinels[i];
			if (sentinel != -1 && list[i].dom.presentValue(sentinel) && vdom.presentValue(sentinel))
				return true;
			Domain dom = list[i].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int va = dom.toVal(a);
				if (vdom.presentValue(va)) {
					listSentinels[i] = va;
					return true;
				}
			}
			return false;
		}

		private boolean validSentinelForValue(int a) {
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

		private boolean reduceDomainOfValue() {
			return vdom.removeIndexesChecking(a -> !validSentinelForValue(a));
		}

		private boolean reduceDomainOfIndex() {
			return idom.removeIndexesChecking(i -> !validSentinelForListAt(i));
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			// If index is not singleton, we try to prune values :
			// - in value's domain, we prune the values which aren't in any of list variables'domains
			// - in index's domain, we prune the values v for which there is no value j such that list[v] and value both have j in their
			// domains
			if (idom.size() > 1) {
				// Update valueSentinels and dom(value)
				if (reduceDomainOfValue() == false)
					return false;
				while (true) {
					// Update listSentinels and dom(index)
					int sizeBefore = idom.size();
					if (reduceDomainOfIndex() == false)
						return false;
					if (sizeBefore == idom.size())
						break;
					// Update valueSentinels and dom(value)
					sizeBefore = vdom.size();
					if (reduceDomainOfValue() == false)
						return false;
					if (sizeBefore == vdom.size())
						break;
				}
			}
			// If index is singleton, we update dom(list[index]) and dom(value) so that they are both equal to the intersection of the two domains
			if (idom.size() == 1) {
				Domain dom = list[idom.unique()].dom;
				if (dom.removeValuesNotIn(vdom) == false || vdom.removeValuesNotIn(dom) == false)
					return false;
				if (dom.size() == 1) {
					assert vdom.size() == 1;
					return entailed();
				}
			}
			return true;
		}

		private boolean controlGAC() {
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
}
