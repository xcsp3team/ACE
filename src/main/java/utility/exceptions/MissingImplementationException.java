/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package utility.exceptions;

/**
 * Such an exception is thrown when a method, required by AbsCon, has not still been implemented.
 */
public class MissingImplementationException extends RuntimeException {
	private static final long serialVersionUID = 1L;

	public MissingImplementationException() {
	}

	public MissingImplementationException(String s) {
		super(s);
	}
}
