/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package interfaces;

public interface ObserverSearch {

	public default void beforeSolving() {}

	public default void beforePreprocessing() {}

	public default void afterPreprocessing() {}

	public default void beforeSearch() {}

	public default void afterSearch() {}

	public default void afterSolving() {}
}
