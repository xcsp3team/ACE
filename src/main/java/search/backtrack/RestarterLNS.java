package search.backtrack;

import static utility.Kit.control;

import java.util.Random;
import java.util.stream.IntStream;

import dashboard.ControlPanel.LargeNeighborhoodSearch;
import search.Restarter;
import search.Solver;
import search.backtrack.RestarterLNS.HeuristicFreezing.Impact;
import search.backtrack.RestarterLNS.HeuristicFreezing.Rand;
import utility.Kit;
import variables.Variable;

// TODO : needs to be fixed : see in 'beforeRun'
public class RestarterLNS extends Restarter {

	private final HeuristicFreezing h;

	public RestarterLNS(Solver solver) {
		super(solver);
		if (solver.rs.cp.lns.freezingHeuristic.equals(Impact.class.getName()))
			this.h = new Impact(this);
		else
			this.h = new Rand(this);
		control(solver instanceof SolverBacktrack, () -> "For LNS, only a SolverBacktrack object can be used.");
	}

	@Override
	public void beforeRun() {
		super.beforeRun();
		int[] solution = solver.solManager.lastSolution;
		if (solution != null) {
			h.freezeVariables(solution);
			for (int i = 0; i < h.freezingSize; i++)
				solver.assign(solver.pb.variables[h.freezingShuffled[i]], solution[h.freezingShuffled[i]]);
			// TODO : while a covered constraint is unsatisfied : remove one assigned frozen variable from irs scope
			// runInitially add all variables, which breaks an assert : how to manage that?
			solver.propagation.runInitially();
		}
	}

	@Override
	public void afterRun() {
		((SolverBacktrack) solver).backtrackToTheRoot();
	}

	// ************************************************************************
	// ***** Heuristics
	// ************************************************************************

	public static abstract class HeuristicFreezing {

		protected final RestarterLNS restarter;

		public final int[] freezingShuffled; // array containing all positions from 0 to pb.variables.length-1, shuffled wrt the heuristic

		public int freezingSize; // equal to the number of variables to freeze

		public HeuristicFreezing(RestarterLNS restarter) {
			this.restarter = restarter;
			int n = restarter.solver.pb.variables.length;
			LargeNeighborhoodSearch setting = restarter.solver.rs.cp.lns;

			this.freezingShuffled = IntStream.range(0, n).toArray();
			if (0 < setting.nVariablesToFreeze && setting.nVariablesToFreeze < n)
				this.freezingSize = restarter.solver.rs.cp.lns.nVariablesToFreeze;
			else if (0 < setting.pVariablesToFreeze && setting.pVariablesToFreeze < 100)
				this.freezingSize = 1 + (setting.pVariablesToFreeze * n) / 100;
			else
				Kit.exit("You must specify the number or percentage of variables to freeze for LNS.");
			Kit.control(0 < freezingSize && freezingSize < restarter.solver.pb.variables.length, () -> "");
		}

		// Implementing Fisher–Yates shuffle (see https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle)
		protected void shuffle() {
			Random random = restarter.solver.rs.random;
			for (int i = freezingShuffled.length - 1; i > 0; i--) {
				int j = random.nextInt(i + 1);
				int tmp = freezingShuffled[i];
				freezingShuffled[i] = freezingShuffled[j];
				freezingShuffled[j] = tmp;
			}
		}

		public abstract void freezeVariables(int[] solution);

		public static class Impact extends HeuristicFreezing {

			private final Variable[] variables;

			private int[] domainSizesBeforeFreezing, domainSizesAfterFreezing;

			public Impact(RestarterLNS restarter) {
				super(restarter);
				this.variables = restarter.solver.pb.variables;
				this.domainSizesBeforeFreezing = new int[variables.length];
				this.domainSizesAfterFreezing = new int[variables.length];

			}

			private void storeDomainSizes(int[] t) {
				for (int i = 0; i < variables.length; i++)
					t[i] = variables[i].dom.size();
			}

			@Override
			public void freezeVariables(int[] solution) {
				shuffle();
				Integer bestImpacted = null;
				for (int i = 0; i < freezingSize; i++) {
					if (bestImpacted != null) {
						int tmp = freezingShuffled[bestImpacted];
						freezingShuffled[bestImpacted] = freezingShuffled[i];
						freezingShuffled[i] = tmp;
					}
					// else we automatically add the first element of shuffled (at position size)
					restarter.solver.assign(variables[freezingShuffled[i]], solution[freezingShuffled[i]]);

					storeDomainSizes(domainSizesBeforeFreezing);
					restarter.solver.propagation.runInitially();
					storeDomainSizes(domainSizesAfterFreezing);

					bestImpacted = null;
					int bestImpact = 0;
					for (int j = i + 1; j < freezingShuffled.length; j++) {
						int impact = domainSizesBeforeFreezing[freezingShuffled[j]] - domainSizesAfterFreezing[freezingShuffled[j]];
						if (impact > bestImpact) {
							bestImpacted = j;
							bestImpact = impact;
						}
					}
				}
				((SolverBacktrack) restarter.solver).backtrackToTheRoot();
			}

		}

		public static class Rand extends HeuristicFreezing {

			public Rand(RestarterLNS restarter) {
				super(restarter);
			}

			@Override
			public void freezeVariables(int[] solution) {
				shuffle();
			}
		}

	}

}
