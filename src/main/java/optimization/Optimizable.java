/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization;

/**
 * An interface for any object (actually, a constraint) that can be used to represent an objective.
 *
 * @author Christophe Lecoutre
 *
 */
public interface Optimizable {

	/**
	 * Returns the current limit/bound of the objective, which is represented by this object
	 * 
	 * @return the current limit/bound of the objective
	 */
	long limit();

	/**
	 * Sets the new limit/bound of the objective, which is represented by this object
	 * 
	 * @param newLimit
	 *            the new limit/bound
	 */
	void setLimit(long newLimit);

	/**
	 * Sets the new limit/bound of the objective, which is represented by this object. A control may be possibly made.
	 * 
	 * @param newLimit
	 *            the new limit/bound
	 */
	default void limit(long newLimit) {
		setLimit(newLimit);
		assert minComputableObjectiveValue() - 1 <= newLimit && newLimit <= maxComputableObjectiveValue() + 1;
	}

	/**
	 * Returns the minimal value of the objective that can be computed according to the initial domains of the involved
	 * variables.
	 * 
	 * @return the minimal value of the objective that can be computed
	 */
	long minComputableObjectiveValue();

	/**
	 * Returns the maximal value of the objective that can be computed according to the initial domains of the involved
	 * variables.
	 * 
	 * @return the maximal value of the objective that can be computed
	 */
	long maxComputableObjectiveValue();

	/**
	 * Returns the minimal value of the objective that can be computed according to the current domains of the involved
	 * variables.
	 * 
	 * @return the minimal value of the objective that can be currently computed
	 */
	long minCurrentObjectiveValue();

	/**
	 * Returns the maximal value of the objective that can be computed according to the current domains of the involved
	 * variables.
	 * 
	 * @return the maximal value of the objective that can be currently computed
	 */
	long maxCurrentObjectiveValue();

	/**
	 * Returns the value of the objective. This method must be called when all involved variables are assigned.
	 * 
	 * @return the value of the objective
	 */
	long objectiveValue();
}
