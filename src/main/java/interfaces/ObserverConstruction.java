/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package interfaces;

public interface ObserverConstruction {

	public default void beforeAnyConstruction() {}

	/**
	 * To be called by the observer when the construction of the problem is finished.
	 */
	public default void onConstructionProblemFinished() {}

	/**
	 * Method to be called by the observer when the construction of the solver is finished.
	 */
	public default void onConstructionSolverFinished() {}
}
