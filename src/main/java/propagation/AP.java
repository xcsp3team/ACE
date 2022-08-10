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
 * 
 * TODO: BUG for java ace WallBuilder-instance.1.xml -jl=10000 -valh=Last -p=AP
 * 
 */
public class AP extends StrongConsistency {

	private final static int GAP = 60;

	private final ESAC3 esac;

	private final SAC sac;

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
			solver.propagation = strong;
			if (strong.runInitially() == false)
				solver.stopping = Stopping.FULL_EXPLORATION;
			time = strong.time;
			solver.propagation = this;
			int after = Variable.nValidValuesFor(solver.problem.variables);
			System.out.println("After running " + strong.getClass().getSimpleName() + " removals=" + (before - after) + " "
					+ Variable.nValidValuesFor(solver.problem.variables));
			propagations.add(strong);
			removals.add(before - after);
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
