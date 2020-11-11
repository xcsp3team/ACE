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

public final class ElementMatrix extends CtrGlobal implements TagUnsymmetric, TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	private Variable[][] matrix;
	private Variable rindex;
	private Variable cindex;
	private int value;

	private Domain rdom, cdom;

	private int rindexPosition; // in scope
	private int cindexPosition; // in scope

	private int[] rsentinels;
	private int[] csentinels;

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
		Kit.control(rindex.dom.areInitValuesExactly(pb.api.range(0, matrix.length)), () -> "case not implemented");
		Kit.control(cindex.dom.areInitValuesExactly(pb.api.range(0, matrix[0].length)), () -> "case not implemented");
		Kit.control(Variable.areAllDistinct(pb.vars(matrix)) && rindex != cindex, () -> Kit.join(matrix) + " " + rindex + " " + cindex);
		rsentinels = new int[matrix.length];
		csentinels = new int[matrix[0].length];
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		// filtering the domain of rindex
		int sizeBefore = rdom.size();
		if (sizeBefore > 1) {
			for (int a = rdom.last(); a != -1; a = rdom.prev(a)) {
				int b = rsentinels[a];
				if (cdom.isPresent(b) && matrix[a][b].dom.isPresentValue(value))
					continue;
				boolean found = false;
				for (b = cdom.last(); b != -1; b = cdom.prev(b)) {
					if (matrix[a][b].dom.isPresentValue(value)) {
						found = true;
						rsentinels[a] = b;
						break;
					}
				}
				if (!found)
					rdom.removeElementary(a);
			}
			if (rdom.afterElementaryCalls(sizeBefore) == false)
				return false;
		}

		// filtering the domain of cindex
		sizeBefore = cdom.size();
		if (sizeBefore > 1) {
			for (int b = cdom.last(); b != -1; b = cdom.prev(b)) {
				int a = csentinels[b];
				if (rdom.isPresent(a) && matrix[a][b].dom.isPresentValue(value))
					continue;
				boolean found = false;
				for (a = rdom.last(); a != -1; a = rdom.prev(a)) {
					if (matrix[a][b].dom.isPresentValue(value)) {
						found = true;
						csentinels[b] = a;
						break;
					}
				}
				if (!found)
					cdom.removeElementary(b);
			}
			if (cdom.afterElementaryCalls(sizeBefore) == false)
				return false;
		}
		// be careful : not a else because of statements above that may modify the domain of indexes
		if (rdom.size() == 1 && cdom.size() == 1)
			if (matrix[rdom.unique()][cdom.unique()].dom.reduceToValue(value) == false)
				return false;
		return true;
	}

}
