/**
 *  AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 *  All rights reserved. 
 *  
 *  This program and the accompanying materials are made 
 *  available under the terms of the CONTRAT DE LICENCE 
 *  DE LOGICIEL LIBRE CeCILL which accompanies this distribution, 
 *  and is available at http://www.cecill.info
 */
package propagation.order2.dual;

import constraints.Constraint;
import propagation.order2.SecondOrderConsistency;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class DualBasedConsistency extends SecondOrderConsistency {

	protected int time;

	protected boolean performingTest;

	protected int[] tmp = new int[2];

	protected boolean isMarkLastDropped(Domain dom) {
		return dom.indexAtMark() == dom.lastRemoved();
	}

	protected void actAfterFirstPropagationStep() {
		Domain.setMarks(solver.pb.variables);
		performingTest = false;
	}

	@Override
	public boolean propagate() {
		// boolean mustMark = preprocessingStage && solver.getVariableManager().getNbPastVariables() == 1;
		while (queue.size() != 0) {
			if (!pickAndFilter())
				return false;
			if (performingTest)
				actAfterFirstPropagationStep();
		}
		return true;
	}

	public DualBasedConsistency(Solver solver) {
		super(solver);
		// TODO verifier que les contraintes binaires soient toutes en extension et telles que removeTuple de ExtensionStructure soit
		// implantée ?
	}

	protected boolean removeTuplesFrom(Variable x, int a, Constraint c) {
		int q = c.scp[0] != x ? 0 : 1;
		Variable y = c.scp[q];
		Domain dy = y.dom;
		if (isMarkLastDropped(dy))
			return false;
		int p = q == 0 ? 1 : 0;
		tmp[p] = a;
		int stop = dy.indexAtMark();
		for (int b = dy.lastRemoved(); b != stop; b = dy.prevRemoved(b)) {
			tmp[q] = b;
			if (!c.removeTuple(tmp))
				throw new AssertionError();
		}
		dy.setMark(); // in order to avoid dealing again with these nogoods later
		return true;
	}

	protected abstract int removeTuplesAfterSingletonTestOn(Variable var, int idx);

	protected boolean singletonTest(Variable x, int a) {
		nSingletonTests++;
		int nbValuesBefore = pb().nValuesRemoved;
		solver.assign(x, a);
		performingTest = true;
		boolean consistent = super.runAfterAssignment(x);
		performingTest = false;
		assert !consistent || controlArcConsistency() : "problem after singleton test: " + x + " = " + a;
		int nbTuplesRemoved = consistent ? removeTuplesAfterSingletonTestOn(x, a) : -1;
		solver.backtrack(x);
		pb().nValuesRemoved = nbValuesBefore;
		if (!consistent) {
			nEffectiveSingletonTests++;
			x.dom.removeElementary(a);
		}
		return nbTuplesRemoved != 0;
	}

	protected boolean performDecisionTestsOf(Variable x) {
		boolean modified = false;
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a))
			if (singletonTest(x, a))
				modified = true;
		return modified;
	}

	protected void updateStructures(Variable uniqueModifiedVariable) {}

	@Override
	public boolean enforceSecondOrderConsistency() {
		int nbValuesBefore = pb().nValuesRemoved;
		int nbNogoodsBefore = solver instanceof SolverBacktrack ? (((SolverBacktrack) solver).learnerNogoods).nNogoods : 0;
		int nbTuplesBefore = nTuplesRemoved;
		int nbConstraintsBefore = solver.pb.constraints.length;
		Variable x = solver.pb.variables[0], markedVar = x;
		do {
			time++;
			if (x.dom.size() > 1) {
				int nb = pb().nValuesRemoved;
				if (performDecisionTestsOf(x)) {
					if (x.dom.size() == 0)
						return false;
					if (!super.runAfterRefutation(x)) // AC must be maintained
						return false;
					updateStructures(pb().nValuesRemoved == nb ? x : null);
					markedVar = x;
				}
			}
			x = solver.pb.variables[(x.num + 1) % solver.pb.variables.length];
			if (x.num == 0)
				displayInfo("after turn", nbConstraintsBefore, nbTuplesBefore, nbNogoodsBefore, nbValuesBefore);
		} while (x != markedVar);
		displayInfo("finally", nbConstraintsBefore, nbTuplesBefore, nbNogoodsBefore, nbValuesBefore);
		return true;
	}

	private void displayInfo(String prefix, int n1, int n2, int n3, int n4) {
		Kit.log.info(prefix + ", nbAddedConstraints=" + (solver.pb.constraints.length - n1) + " nbTuplesRemoved=" + (nTuplesRemoved - n2)
				+ (solver instanceof SolverBacktrack ? " nbNogoodsRemoved=" + ((((SolverBacktrack) solver).learnerNogoods).nNogoods - n3) : "")
				+ " nbValuesRemoved=" + (pb().nValuesRemoved - n4));
	}
}
