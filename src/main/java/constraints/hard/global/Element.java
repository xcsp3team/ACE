/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import static org.xcsp.common.Types.TypeConditionOperatorSet.NOTIN;

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.hard.CtrGlobal;
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
	protected final Variable index;
	protected final int indexPosition; // in scope

	public Element(Problem pb, Variable[] list, int startAt, Variable index, Object value) {
		super(pb, Utilities.collect(Variable.class, list, index, value)); // before, was collectDistinct (but put in the constructor of Constraint)
		this.list = list;
		this.startAt = startAt;
		this.index = index;
		this.indexPosition = IntStream.range(0, scp.length).filter(i -> scp[i] == index).findFirst().getAsInt();
		Kit.control(startAt == 0, () -> "Starting at a value different from 0 not implemented yet");
		Kit.control(Variable.areAllDistinct(list) && index != value, () -> "i=" + index + " x=" + Kit.join(list) + " v=" + value);
		// Kit.control(this instanceof ElementConstant || Stream.of(list).allMatch(x -> x != index), () -> "i=" + index + " X=" + Kit.join(list) + "
		// v=" + value);
		Kit.control(index.dom.areInitValuesExactly(pb.api.range(startAt, startAt + list.length)), () -> " pb with " + this + " " + startAt);
	}

	// returns the domain of the variable in list whose position is given by the specified integer (note that startAt is paid attention to)
	protected Domain domAt(int i) {
		return list[i - startAt].dom;
	}

	// ************************************************************************
	// ***** Constraint ElementConstant
	// ************************************************************************

	public static class ElementConstant extends Element implements TagFilteringCompleteAtEachCall {
		private final int value;

		@Override
		public boolean checkValues(int[] t) {
			return t[t[indexPosition] - startAt] == value;
		}

		public ElementConstant(Problem pb, Variable[] list, int startAt, Variable index, int value) {
			super(pb, list, startAt, index, value);
			this.value = value;
			defineKey(value, startAt);
			Kit.control(Variable.areAllDomainsContainingValue(list, value));
			if (indexPosition < list.length && indexPosition + startAt != value) // special case (index in list)
				index.dom.removeValueAtConstructionTime(value);
		}

		public ElementConstant(Problem pb, Variable[] list, Variable index, int value) {
			this(pb, list, 0, index, value);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (index.dom.size() > 1) // checking that the values of index are still valid
				if (index.dom.removeIndexesChecking(a -> !domAt(a).isPresentValue(value)) == false)
					return false;
			// be careful : not a else because of statements above that may modify the domain of index
			if (index.dom.size() == 1)
				if (domAt(index.dom.unique()).reduceToValue(value) == false)
					return false;
			return true;
		}
	}

	// ************************************************************************
	// ***** Constraint ElementVariable
	// ************************************************************************

	/**
	 * Such a constraint is satisfied iff list[index] = value
	 */
	public static class ElementVariable extends Element implements TagFilteringCompleteAtEachCall {
		private final Variable value;

		private final int valuePosition; // in scope

		@Override
		public boolean checkValues(int[] t) {
			return t[t[indexPosition] - startAt] == t[valuePosition];
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
			this.value = value;
			this.valuePosition = IntStream.range(0, scp.length).filter(i -> scp[i] == value).findFirst().getAsInt();
			this.valueSentinels = Kit.repeat(-1, value.dom.initSize());
			this.listSentinels = Kit.repeat(-1, list.length);
			defineKey();
			// TODO control qu'un des éléments du domaine de result est dans chaque domaine des variables de vector ?
		}

		public ElementVariable(Problem pb, Variable[] list, Variable index, Variable value) {
			this(pb, list, 0, index, value);
		}

		private boolean findSentinelForListAt(int i) {
			return domAt(i).iterateOnValuesStoppingWhen(v -> {
				boolean present = value.dom.isPresentValue(v);
				if (present)
					listSentinels[i] = v;
				return present;
			});
		}

		private boolean findSentinelForValue(int a) {
			int v = value.dom.toVal(a);
			return index.dom.iterateStoppingWhen(i -> {
				boolean present = domAt(i).toPresentIdx(v) >= 0;
				if (present)
					valueSentinels[a] = i;
				return present;
			});
		}

		private boolean reduceDomainOfValue() {
			return value.dom.removeIndexesChecking(a -> {
				int sentinel = valueSentinels[a];
				return (sentinel == -1 || !index.dom.isPresent(sentinel) || !domAt(sentinel).isPresentValue(value.dom.toVal(a))) && !findSentinelForValue(a);
			});
		}

		private boolean reduceDomainOfIndex() {
			return index.dom.removeIndexesChecking(i -> {
				int sentinel = listSentinels[i];
				return (sentinel == -1 || !domAt(i).isPresentValue(sentinel) || !value.dom.isPresentValue(sentinel)) && !findSentinelForListAt(i);
			});
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			// If index is not singleton, we try to prune values :
			// - in value's domain, we prune the values which aren't in any of list variables'domains
			// - in index's domain, we prune the values v for which there is no value j such that list[v] and value both have j in their
			// domains
			if (index.dom.size() > 1) {
				// Update valueSentinels and dom(value)
				if (reduceDomainOfValue() == false)
					return false;
				while (true) {
					// Update listSentinels and dom(index)
					int sizeBefore = index.dom.size();
					if (reduceDomainOfIndex() == false)
						return false;
					if (sizeBefore == index.dom.size())
						break;
					// Update valueSentinels and dom(value)
					sizeBefore = value.dom.size();
					if (reduceDomainOfValue() == false)
						return false;
					if (sizeBefore == value.dom.size())
						break;
				}
			}
			// If index is singleton, we update dom(list[index]) and dom(value) so that they are both equal to the intersection of the two domains
			if (index.dom.size() == 1) {
				Domain dom = domAt(index.dom.unique());
				if (dom.removeValues(NOTIN, value.dom) == false || value.dom.removeValues(NOTIN, dom) == false)
					return false;
			}
			assert controlGAC();
			return true;
		}

		private boolean controlGAC() {
			Kit.control(index.dom.size() != 1 || domAt(index.dom.unique()).subsetOf(value.dom),
					() -> "index is singleton and dom(index) is not included in dom(result).");
			for (int a = index.dom.first(); a != -1; a = index.dom.next(a))
				Kit.control(domAt(a).overlapWith(value.dom), () -> "One var has no value in dom(result).");
			for (int a = value.dom.first(); a != -1; a = value.dom.next(a)) {
				int v = value.dom.toVal(a);
				int b;
				for (b = index.dom.first(); b != -1; b = index.dom.next(b))
					if (domAt(b).isPresentValue(v))
						break;
				Kit.control(b != -1, () -> "value " + v + " is in dom(value) but in no list variable whose index is still in dom(index).");
			}
			return true;
		}

	}
}
