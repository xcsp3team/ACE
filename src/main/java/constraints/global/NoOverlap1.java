package constraints.global;

import static utility.Kit.control;

import java.util.stream.IntStream;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Variable;

public final class NoOverlap1 extends ConstraintGlobal implements TagNotAC {

	@Override
	public boolean isSatisfiedBy(int[] tuple) {
		for (int i = 0; i < tuple.length; i++)
			for (int j = i + 1; j < tuple.length; j++)
				if (!(tuple[i] + widths[i] <= tuple[j] || tuple[j] + widths[j] <= tuple[i]))
					return false;
		return true;
	}

	private int[] widths;

	private SetSparseReversible relevantTasks; // currently relevant tasks

	private long volume;
	private long margin;

	public NoOverlap1(Problem pb, Variable[] origins, int[] widths) {
		super(pb, origins);
		control(origins.length > 1 && origins.length == widths.length);
		this.widths = widths;

		int horizon = IntStream.range(0, scp.length).map(i -> scp[i].dom.lastValue() + widths[i]).max().getAsInt();

		this.volume = IntStream.of(widths).sum();
		this.margin = horizon - volume;
	}

	@Override
	public boolean runPropagator(Variable x) {
		int depth = problem.solver.depth();

		// we compute the relevant time bounds: minimum relevant start time and maximum relevant end time from current
		// future variables
		int smin = Integer.MAX_VALUE, emax = Integer.MIN_VALUE;
		for (int j = futvars.limit; j >= 0; j--) {
			int i = futvars.dense[j];
			smin = Math.min(smin, scp[i].dom.firstValue());
			emax = Math.max(emax, scp[i].dom.lastValue() + widths[i]);
		}
		// we update the set of relevant tasks to consider from (smin,emax)
		for (int j = relevantTasks.limit; j >= 0; j--) {
			int i = relevantTasks.dense[j];
			if (scp[i].dom.size() == 1 && (scp[i].dom.lastValue() + widths[i] <= smin || emax <= scp[i].dom.firstValue()))
				relevantTasks.removeAtPosition(j, depth);
		}
		return true;
	}
}
