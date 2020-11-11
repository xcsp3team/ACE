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
import constraints.extension.CtrExtension;
import interfaces.FilteringSpecific;
import propagation.order2.SecondOrderConsistency;
import search.Solver;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class SDC2 extends SecondOrderConsistency {

	private int[] lastModifications;

	private int counter;

	public SDC2(Solver solver) {
		super(solver);
		// if (solver.problem.getMaxConstraintArity() > 2 || solver.problem.getMinConstraintArity() < 2)
		// throw new IncompatiblePropertiesException();
		// verifier que les contraintes soient toutes en extension
		// if (solver.constraints.length != solver.variables.length * (solver.variables.length - 1) / 2)
		// throw new IncompatiblePropertiesException();
		lastModifications = new int[solver.pb.variables.length];
	}

	private int removeConservativelyTuplesFrom(Variable x, int a) {
		int before = nTuplesRemoved;
		for (Constraint c : x.ctrs) {
			if (c.scp.length != 2 || !(c instanceof CtrExtension))
				continue;
			int p = c.positionOf(x);
			int q = (p == 0 ? 1 : 0);
			Variable y = c.scp[q];
			int[] tmp = c.tupleManager.localTuple;
			tmp[p] = a;
			Domain dom = y.dom;
			for (int b = dom.lastRemoved(); b != -1; b = dom.prevRemoved(b)) {
				if (dom.isRemovedAtLevel(b, 0)) // getAbsentLevelOf(brotherIndex) == 0)
					break;
				tmp[q] = b;
				if (!c.removeTuple(tmp))
					break; // since all other values are either already FC inconsistent or definitively removed
				lastModifications[y.num] = counter;
			}
		}
		return nTuplesRemoved - before; // nbTuplesRemoved;
	}

	protected final boolean singletonTest(Variable x, int a) {
		Variable[] variables = solver.pb.variables;
		nSingletonTests++;
		int before = pb().nValuesRemoved;
		solver.assign(x, a);
		boolean consistent = true;
		if (counter <= variables.length) {
			consistent = super.runAfterAssignment(x);
		} else {
			for (Constraint c : x.ctrs) {
				if (c instanceof FilteringSpecific) {
					// if (! isConsistent(var,ctr)) { // que fait-il faire ?
					// consistent = false;
					// break;
					// }
					throw new UnsupportedOperationException();

				} else {
					Variable y = Variable.firstDifferentVariableIn(c.scp, x);
					reviser.applyTo(c, y);
					if (y.dom.size() == 0) {
						consistent = false;
						break;
					}
				}

				// int[] tuple = constraint.getTupleManager().localTuple;
				// int pos = constraint.getInvolvedVariable(0) == futureVariable ? 0 : 1;
				// int bro = pos == 0 ? 1 : 0;
				// tuple[pos] = index;
				// constraint.getTupleManager().setCurrentTuple(tuple);
				//
				// Variable brotherVariable = constraint.getInvolvedVariable(bro);
				// Domain domain = brotherVariable.domain;
				// Elements elements = domain.getElements();
				// for (int index2 = elements.getFirstPresent(); index2 != -1; index2 = elements.getNextPresent(index2)) {
				// tuple[bro] = index2;
				// if (!constraint.checkCurrentTupleOfAssistant())
				// domain.removeElementAt(index2);
				// }
				// if (elements.getNbPresentElements() == 0) {
				// consistent = false;
				// break;
				// }

			}
			int id = x.num;
			int lastCheck = counter - variables.length;
			for (int i = 0; i < lastModifications.length; i++)
				if (i != id && lastModifications[i] > lastCheck)
					queue.add(variables[i]);
			queue.incrementTimestampsOfEnqueuedVariables();
			consistent = (consistent && propagate());
		}

		// boolean consistent = super.checkConsistencyAfterAssignmentOf(futureVariable);
		assert !consistent || controlArcConsistency() : "problem after singleton test: " + x + " = " + a;
		int nbTuplesRemoved = consistent ? removeConservativelyTuplesFrom(x, a) : -1;

		solver.backtrack(x);
		pb().nValuesRemoved = before;

		if (!consistent) {
			nEffectiveSingletonTests++;
			x.dom.removeElementary(a);
			// System.out.println("Sac removal of " + variable + " " + index + " nbRe=" + Domain.getNbRemovals());
		}
		return nbTuplesRemoved != 0;
	}

	private boolean performSingletonTestsOf(Variable x) {
		boolean modified = false;
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a))
			if (singletonTest(x, a))
				modified = true;
		return modified;
	}

	@Override
	public boolean enforceSecondOrderConsistency() {
		Variable x = solver.pb.variables[0];
		Variable lastEffectiveVar = x;
		do {
			counter++;
			if (x.dom.size() > 1) {
				int before = pb().nValuesRemoved;
				if (performSingletonTestsOf(x)) {
					lastModifications[x.num] = counter;
					if (x.dom.size() == 0)
						return false;
					if (!super.runAfterRefutation(x)) // AC must be maintained
						return false;
					if (pb().nValuesRemoved != before)
						for (Variable y : solver.pb.variables)
							lastModifications[y.num] = counter;
					lastEffectiveVar = x;
				}
				if (solver.finished())
					return true;
			}
			x = solver.pb.variables[x.num == solver.pb.variables.length - 1 ? 0 : x.num + 1];
			if (x.num == 0)
				Kit.log.info("after turn, nbTuplesRemoved=" + nTuplesRemoved + " nbValuesRemoved=" + pb().nValuesRemoved);
		} while (x != lastEffectiveVar);
		Kit.log.info("finished, nbTuplesRemoved=" + nTuplesRemoved + " nbValuesRemoved=" + pb().nValuesRemoved);
		return true;
	}
}
