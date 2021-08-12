package solver;

import java.text.NumberFormat;

import interfaces.Observers.ObserverDecisions;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import propagation.Forward;
import utility.Kit.Stopwatch;
import variables.Variable;

/**
 * This class allows us to gath all statistics of a solver.
 * 
 * @author Christophe Lecoutre
 */
public final class Statistics implements ObserverSearch, ObserverRuns, ObserverDecisions {

	public static NumberFormat nformat = NumberFormat.getInstance();

	/*************************************************************************
	 ***** Implemented Interfaces
	 *************************************************************************/

	@Override
	public final void beforePreprocessing() {
		stopwatch.start();
		nPreproAddedNogoods = solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods : 0;
		nPreproAddedCtrs = solver.problem.constraints.length;
	}

	@Override
	public final void afterPreprocessing() {
		preproWck += stopwatch.wckTime();
		nPreproAddedNogoods = solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods - nPreproAddedNogoods : 0;
		nPreproAddedCtrs = solver.problem.constraints.length - nPreproAddedCtrs;
		nPreproRemovedValues = Variable.nRemovedValuesFor(solver.problem.variables);
		nPreproRemovedTuples = solver.propagation.nTuplesRemoved;
	}

	@Override
	public final void beforeSolving() {
		stopwatch.start();
	}

	@Override
	public final void afterSolving() {
		solvingWck += stopwatch.wckTime();
	}

	@Override
	public void afterRun() {
		searchWck = stopwatch.wckTime();
	}

	@Override
	public void beforePositiveDecision(Variable x, int a) {
		nNodes++;
		if (x.dom.size() > 1)
			nDecisions++;
		// nAssignments++; done elsewhere
	}

	@Override
	public void beforeNegativeDecision(Variable x, int a) {
		if (x.dom.size() > 1) {
			nNodes++;
			nDecisions++;
		}
	}

	/*************************************************************************
	 ***** Fields and Methods
	 *************************************************************************/

	/**
	 * The solver to which the object is attached
	 */
	public final Solver solver;

	/**
	 * A stopwatch used to compute the time taken by some operations (e.g., construction of the problem or solver)
	 */
	public final Stopwatch stopwatch = new Stopwatch();

	public long nNodes = 1, nDecisions, nWrongDecisions, nBacktracks, nAssignments, nFailedAssignments;

	public long nPreproRemovedValues, nPreproRemovedTuples, nPreproAddedCtrs, nPreproAddedNogoods;

	public long solvingWck, preproWck, searchWck, firstSolWck, firstSolCpu, lastSolWck, lastSolCpu;

	private long tmpNbAssignments, tmpNbBacktracks, tmpNbFailedAssignments;

	public Statistics(Solver solver) {
		this.solver = solver;
	}

	public long numberSafe() {
		return nNodes + nAssignments + nBacktracks;
	}

	public void store() {
		tmpNbAssignments = nAssignments;
		tmpNbFailedAssignments = nFailedAssignments;
		tmpNbBacktracks = nBacktracks;
	}

	public void restore() {
		nAssignments = tmpNbAssignments;
		nFailedAssignments = tmpNbFailedAssignments;
		nBacktracks = tmpNbBacktracks;
	}

	public final long nRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nRevisions : 0;
	}

	public final long nUselessRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nUselessRevisions : 0;
	}

	public void manageSolution() {
		long cpu = solver.head.stopwatch.cpuTime(), wck = solver.head.instanceStopwatch.wckTime();
		if (solver.solutions.found == 1) {
			firstSolCpu = cpu;
			firstSolWck = wck;
		}
		lastSolCpu = cpu;
		lastSolWck = wck;
	}

}