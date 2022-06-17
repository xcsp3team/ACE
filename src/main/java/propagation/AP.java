/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import java.util.ArrayList;
import java.util.List;

import propagation.SAC.ESAC3;
import propagation.SAC.SAC3;
import solver.Solver;
import solver.Solver.Stopping;
import variables.Variable;

/**
 * This is the class ...
 */
public class AP extends StrongConsistency {

	private final static int GAP = 60;

	private ESAC3 esac;

	private SAC sac;

	private final Propagation[] alternatives;

	private List<Propagation> propagations = new ArrayList<>();

	private List<Integer> removals = new ArrayList<>();

	public AP(Solver solver) {
		super(solver);
		this.esac = new ESAC3(solver);
		this.sac = new SAC3(solver);
		this.alternatives = new Propagation[] { esac, sac };
	}

	@Override
	protected boolean enforceStrongConsistency() {
		throw new AssertionError("not relevant for this adaptative filtering procedure");
	}

	private Propagation whichStrongPropagation() {
		return alternatives[propagations.size() % alternatives.length];
	}

	@Override
	public boolean runInitially() {
		return enforceAC();
	}

	@Override
	public boolean runPossiblyAtRoot() {
		boolean rerun = super.runPossiblyAtRoot();
		if (solver.stopping == Stopping.FULL_EXPLORATION)
			return rerun;
		int numRun = solver.restarter.numRun;
		if (0 < numRun && numRun % GAP == 0) {
			int before = Variable.nValidValuesFor(solver.problem.variables);
			Propagation strong = whichStrongPropagation();
			strong.time = time;
			// for (Constraint c : solver.problem.constraints)
			// c.time = 0;
			// TODO propagation() in Domain not using the right object ? TO TEST
			// for (Variable x : solver.problem.variables)
			// x.time = 0;
			solver.propagation = strong;
			if (strong.runInitially() == false)
				solver.stopping = Stopping.FULL_EXPLORATION;
			time = strong.time;
			solver.propagation = this;
			int nRemovals = before - Variable.nValidValuesFor(solver.problem.variables);
			System.out.println(
					"After running " + strong.getClass().getSimpleName() + " removals=" + nRemovals + " " + Variable.nValidValuesFor(solver.problem.variables));
			// System.out.println("nb singleton checks " + strong.nSingletonTests);
			propagations.add(strong);
			removals.add(nRemovals);
			rerun = true;
		}
		return rerun;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return enforceACafterAssignment(x);
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		return enforceACafterRefutation(x);
	}
}
