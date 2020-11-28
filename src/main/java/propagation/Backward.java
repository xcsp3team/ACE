/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.stream.Stream;

import org.xcsp.common.Types.TypeFramework;

import constraints.Constraint;
import optimization.LowerBoundCapability;
import solver.Solver;
import utility.Kit;
import variables.Variable;

/**
 * This class gives the description of a backward propagation technique. <br>
 * Such a propagation technique corresponds to a retrospective approach which works with past variables. The domains of the future variables are not modified.
 */
public abstract class Backward extends Propagation {

	public Backward(Solver solver) {
		super(solver);
	}

	@Override
	public final boolean runInitially() {
		return true; // nothing to do at pre-processing
	}

	@Override
	public final boolean runAfterRefutation(Variable x) {
		return true; // nothing to do when refuting a value
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * The basic BT Algorithm.
	 */
	public static final class BT extends Backward {

		public BT(Solver solver) {
			super(solver);
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			assert x.assigned();
			return Stream.of(solver.problem.constraints).allMatch(c -> c.ignored || c.futvars.size() > 0 || c.seekFirstSupport());
		}
	}

	/**
	 * The is a class for <i>generate and test</i>.
	 */
	public static final class GT extends Backward {
		public GT(Solver solver) {
			super(solver);
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			assert x.assigned();
			return solver.futVars.size() > 0 || Stream.of(solver.problem.constraints).allMatch(c -> c.ignored || c.seekFirstSupport());
		}
	}

	public static final class BTSoft extends Backward implements LowerBoundCapability {

		@Override
		public final long getLowerBound() {
			return Constraint.costOfCoveredConstraintsIn(solver.problem.constraints);
		}

		public BTSoft(Solver solver) {
			super(solver);
			Kit.control(solver.problem.settings.framework == TypeFramework.MAXCSP, () -> "MaxCSP is not indicated in your settings");
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			return Constraint.costOfCoveredConstraintsIn(solver.problem.constraints) < solver.solManager.bestBound;
		}

	}

	public static final class GTSoft extends Backward implements LowerBoundCapability {

		@Override
		public final long getLowerBound() {
			return Constraint.costOfCoveredConstraintsIn(solver.problem.constraints);
		}

		public GTSoft(Solver solver) {
			super(solver);
			Kit.control(solver.problem.settings.framework == TypeFramework.MAXCSP, () -> "MaxCSP is not indicated in your settings");
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			assert x.assigned();
			if (solver.futVars.size() == 0)
				return Constraint.costOfCoveredConstraintsIn(solver.problem.constraints) < solver.solManager.bestBound;
			return true;
		}
	}

}
