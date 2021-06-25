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

public abstract class ElementMatrix extends CtrGlobal implements TagNotSymmetric, TagAC, TagFilteringCompleteAtEachCall {

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
		// control(scp.length == n * m + 2 + (value instanceof Variable ? 1 : 0)); // TODO relax this (no twice occurrences of the same variable)? to which
		// extent?
		rdom.removeValuesAtConstructionTime(v -> v < 0 || v >= n);
		cdom.removeValuesAtConstructionTime(v -> v < 0 || v >= m);
	}

	// ************************************************************************
	// ***** Constraint ElementMatrixConstant
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
	// ***** Constraint ElementMatrixVariable
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
