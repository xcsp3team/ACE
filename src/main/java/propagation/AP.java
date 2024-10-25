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
import utility.Kit;
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

	private int coeff = 1;

	private final Propagation[] alternatives;

	private List<Propagation> propagations = new ArrayList<>();

	private List<Integer> removals = new ArrayList<>();

	public AP(Solver solver) {
		super(solver);
		this.esac = new ESAC3(solver);
		this.esac.limitedEnforcment = 10;
		this.sac = new SAC3(solver);
		this.alternatives = new Propagation[] { esac, sac };
	}

	@Override
	protected boolean enforceStrongConsistency() {
		throw new AssertionError("not relevant for this adaptative filtering procedure");
	}

	private Propagation whichStrongPropagation() {
		Propagation p = alternatives[propagations.size() % alternatives.length];
		if (p instanceof SAC3 && Variable.nValidValuesFor(solver.problem.variables) > 10000)
			p = esac;
		return p;
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
		if (0 < numRun && numRun % (GAP * coeff) == 0) {
			int before = Variable.nValidValuesFor(solver.problem.variables);
			Propagation strong = whichStrongPropagation();
			strong.time = time;
			solver.propagation = strong;
			if (strong.runInitially() == false)
				solver.stopping = Stopping.FULL_EXPLORATION;
			time = strong.time;
			solver.propagation = this;
			int after = Variable.nValidValuesFor(solver.problem.variables);
			int nRemovals = before - after;
			if (strong == sac)
				coeff = nRemovals == 0 ? coeff + 1 : Math.max(1, coeff - 1);
			System.out.println(Kit.Color.YELLOW.coloring(" ...filtering " + strong.getClass().getSimpleName()) + " removals=" + nRemovals + " coeff=" + coeff);
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
