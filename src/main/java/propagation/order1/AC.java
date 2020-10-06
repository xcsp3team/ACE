/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the
 * terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies
 * this distribution, and is available at http://www.cecill.info
 */
package propagation.order1;

import java.util.stream.Stream;

import constraints.Constraint;
import propagation.order1.FailedValueBasedConsistency.ArcFailedValueConsistency;
import propagation.order1.FailedValueBasedConsistency.FailedValueConsistency;
import propagation.order1.FailedValueBasedConsistency.PartialArcFailedValueConsistency;
import propagation.order1.isomorphism.PropagationIsomorphism;
import search.Solver;
import variables.Variable;

public class AC extends PropagationForward {

	/**
	 * Indicates if GAC is guaranteed, either by a generic scheme that does not requires to wait for a certain number of assigned, or by a global
	 * constraint.
	 */
	public final boolean guaranteed;

	/**
	 * The number of deleted values at preprocessing, by AC.
	 */
	public int nPreproRemovals;

	/**
	 * Additional consistency enforced after positive decisions. Possibly, null.
	 */
	public final FailedValueBasedConsistency fvbc;

	public AC(Solver solver) {
		super(solver);
		this.guaranteed = Constraint.isGuaranteedGACOn(solver.pb.constraints);
		String s = cp().propagating.classForFailedValues;
		if (s == null || s.length() == 0)
			this.fvbc = null;
		else if (s.equals("FailedValueConsistency"))
			this.fvbc = new FailedValueConsistency(this);
		else if (s.equals("PartialArcFailedValueConsistency"))
			this.fvbc = new PartialArcFailedValueConsistency(this);
		else if (s.equals("ArcFailedValueConsistency"))
			this.fvbc = new ArcFailedValueConsistency(this);
		else
			this.fvbc = null;
	}

	/**
	 * Can be called by subclasses to enforce AC.
	 */
	public final boolean enforceArcConsistency() {
		int nBefore = pb().nValuesRemoved;
		queue.fill();
		boolean consistent = propagate();
		nPreproRemovals = pb().nValuesRemoved - nBefore;
		if (!consistent)
			return false;
		assert controlArcConsistency();
		return true;
	}

	@Override
	public boolean runInitially() {
		return enforceArcConsistency();
	}

	/**
	 * Can be called by subclasses to enforce AC.
	 */
	public final boolean enforceArcConsistencyAfterAssignment(Variable x) {
		assert x.isAssigned() && (queue.size() == 0 || this instanceof PropagationIsomorphism) : queue.size() + " " + x.isAssigned();
		if (getClass() != AC.class || x.dom.isModifiedAtCurrentDepth() || !guaranteed || !hasSolverPropagatedAfterLastButOneDecision()) {
			queue.add(x);
			if (propagate() == false)
				return false;
		}
		assert controlArcConsistency();
		return fvbc != null ? fvbc.enforce() : true;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return enforceArcConsistencyAfterAssignment(x);
	}

	/**
	 * Can be called by suclasses to enforce AC.
	 */
	public boolean enforceArcConsistencyAfterRefutation(Variable x) {
		if (!super.runAfterRefutation(x))
			return false;
		assert controlArcConsistency();
		return true;
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		return enforceArcConsistencyAfterRefutation(x);
	}

	public boolean controlArcConsistency() {
		return !guaranteed || Stream.of(solver.pb.constraints).allMatch(c -> c.controlArcConsistency());
	}
}
