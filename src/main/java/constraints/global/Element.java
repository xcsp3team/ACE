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

import constraints.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class Element extends CtrGlobal implements TagUnsymmetric, TagGACGuaranteed {

	protected final Variable[] list;
	protected final int startAt;
	protected final Variable ivar; // index variable
	protected final Domain idom;
	protected final int ipos; // index position in scope

	public Element(Problem pb, Variable[] list, int startAt, Variable index, Object value) {
		super(pb, Utilities.collect(Variable.class, list, index, value)); // before, was collectDistinct (but put in the constructor of Constraint)
		this.list = list;
		this.startAt = startAt;
		this.ivar = index;
		this.idom = index.dom;
		this.ipos = IntStream.range(0, scp.length).filter(i -> scp[i] == index).findFirst().getAsInt();
		control(startAt == 0, "Starting at a value different from 0 not implemented yet");
		control(Variable.areAllDistinct(list) && index != value, "i=" + index + " x=" + Kit.join(list) + " v=" + value);
		// control(this instanceof ElementConstant || Stream.of(list).allMatch(x -> x != index), "i=" + index + " X=" + Kit.join(list) + "
		// v=" + value);
		control(idom.areInitValuesExactly(pb.api.range(startAt, startAt + list.length)), " pb with " + this + " " + startAt);
	}

	// returns the domain of the variable in list whose position is given by the specified integer (note that startAt is paid attention to)
	protected Domain domAt(int i) {
		return list[i - startAt].dom;
	}

	// ************************************************************************
	// ***** Constraint ElementConstant
	// ************************************************************************

	public static class ElementConstant extends Element implements TagFilteringCompleteAtEachCall {
		private final int k;

		@Override
		public boolean checkValues(int[] t) {
			return t[t[ipos] - startAt] == k;
		}

		public ElementConstant(Problem pb, Variable[] list, int startAt, Variable index, int value) {
			super(pb, list, startAt, index, value);
			this.k = value;
			defineKey(value, startAt);
			control(Variable.areAllDomainsContainingValue(list, k));
			if (ipos < list.length && ipos + startAt != k) // special case (index in list)
				idom.removeValueAtConstructionTime(k);
		}

		public ElementConstant(Problem pb, Variable[] list, Variable index, int value) {
			this(pb, list, 0, index, value);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (idom.size() > 1) // checking that the values of index are still valid
				if (idom.removeIndexesChecking(a -> !domAt(a).isPresentValue(k)) == false)
					return false;
			// be careful : not a else because of statements above that may modify the domain of index
			return idom.size() > 1 || domAt(idom.unique()).reduceToValue(k);
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
			return t[t[ipos] - startAt] == t[vpos];
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
			// TODO control qu'un des éléments du domaine de result est dans chaque domaine des variables de vector ?
		}

		public ElementVariable(Problem pb, Variable[] list, Variable index, Variable value) {
			this(pb, list, 0, index, value);
		}

		private boolean findSentinelForListAt(int i) {
			Domain dom = domAt(i);
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int v = dom.toVal(a);
				if (vdom.isPresentValue(v)) {
					listSentinels[i] = v;
					return true;
				}
			}
			return false;
		}

		private boolean findSentinelForValue(int a) {
			int v = vdom.toVal(a);
			for (int i = idom.first(); i != -1; i = idom.next(i)) {
				if (domAt(i).isPresentValue(v)) {
					valueSentinels[a] = i;
					return true;
				}
			}
			return false;
		}

		private boolean reduceDomainOfValue() {
			return vdom.removeIndexesChecking(a -> {
				int sentinel = valueSentinels[a];
				return (sentinel == -1 || !idom.isPresent(sentinel) || !domAt(sentinel).isPresentValue(vdom.toVal(a))) && !findSentinelForValue(a);
			});
		}

		private boolean reduceDomainOfIndex() {
			return idom.removeIndexesChecking(i -> {
				int sentinel = listSentinels[i];
				return (sentinel == -1 || !domAt(i).isPresentValue(sentinel) || !vdom.isPresentValue(sentinel)) && !findSentinelForListAt(i);
			});
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
				Domain dom = domAt(idom.unique());
				if (dom.removeValuesNotIn(vdom) == false || vdom.removeValuesNotIn(dom) == false)
					return false;
			}
			assert controlGAC();
			return true;
		}

		private boolean controlGAC() {
			Kit.control(idom.size() != 1 || domAt(idom.unique()).subsetOf(vdom), () -> "index is singleton and dom(index) is not included in dom(result).");
			for (int a = idom.first(); a != -1; a = idom.next(a))
				Kit.control(domAt(a).overlapWith(vdom), () -> "One var has no value in dom(result).");
			for (int a = vdom.first(); a != -1; a = vdom.next(a)) {
				int v = vdom.toVal(a);
				int b;
				for (b = idom.first(); b != -1; b = idom.next(b))
					if (domAt(b).isPresentValue(v))
						break;
				Kit.control(b != -1, () -> "value " + v + " is in dom(value) but in no list variable whose index is still in dom(index).");
			}
			return true;
		}

	}
}
