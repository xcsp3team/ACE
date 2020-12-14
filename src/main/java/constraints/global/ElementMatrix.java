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
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class ElementMatrix extends CtrGlobal implements TagUnsymmetric, TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	private Variable[][] matrix;
	private Variable rindex, cindex;
	private int value;

	private Domain rdom, cdom;

	private int rindexPosition, cindexPosition; // in scope

	private int[] rsentinels, csentinels;

	@Override
	public boolean checkValues(int[] t) {
		int i = t[rindexPosition], j = t[cindexPosition];
		return t[i * matrix.length + j] == value;
	}

	public ElementMatrix(Problem pb, Variable[][] matrix, Variable rindex, Variable cindex, int value) {
		super(pb, Utilities.collect(Variable.class, matrix, rindex, cindex));
		this.matrix = matrix;
		this.rindex = rindex;
		this.cindex = cindex;
		this.value = value;
		this.rdom = rindex.dom;
		this.cdom = cindex.dom;
		defineKey(value);
		this.rindexPosition = IntStream.range(0, scp.length).filter(i -> scp[i] == rindex).findFirst().getAsInt();
		this.cindexPosition = IntStream.range(0, scp.length).filter(i -> scp[i] == cindex).findFirst().getAsInt();
		control(rindex.dom.areInitValuesExactly(pb.api.range(0, matrix.length)), () -> "case not implemented");
		control(cindex.dom.areInitValuesExactly(pb.api.range(0, matrix[0].length)), () -> "case not implemented");
		control(Variable.areAllDistinct(pb.vars(matrix)) && rindex != cindex, () -> Kit.join(matrix) + " " + rindex + " " + cindex);
		this.rsentinels = new int[matrix.length];
		this.csentinels = new int[matrix[0].length];
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		// filtering the domain of rindex
		int sizeBefore = rdom.size();
		if (sizeBefore > 1) {
			extern: for (int a = rdom.last(); a != -1; a = rdom.prev(a)) {
				int b = rsentinels[a];
				if (cdom.present(b) && matrix[a][b].dom.isPresentValue(value))
					continue;
				for (b = cdom.last(); b != -1; b = cdom.prev(b))
					if (matrix[a][b].dom.isPresentValue(value)) {
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
				if (rdom.present(a) && matrix[a][b].dom.isPresentValue(value))
					continue;
				for (a = rdom.last(); a != -1; a = rdom.prev(a)) {
					if (matrix[a][b].dom.isPresentValue(value)) {
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
		return rdom.size() > 1 || cdom.size() > 1 || (matrix[rdom.unique()][cdom.unique()].dom.reduceToValue(value) && entailed());
	}
}
