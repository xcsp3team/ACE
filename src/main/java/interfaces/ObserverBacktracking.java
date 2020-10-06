/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package interfaces;

public interface ObserverBacktracking {
	void restoreBefore(int depthBeforeBacktrack);

	// public default void setMark() {
	// throw new MissingImplementationException();
	// }
	//
	// public default void restoreAtMark() {
	// throw new MissingImplementationException();
	// }

	interface ObserverBacktrackingSystematic extends ObserverBacktracking {
	}

	interface ObserverBacktrackingUnsystematic extends ObserverBacktracking {
		int lastModificationDepth();
	}

}
