/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package tools.random;

public class Thresholds {

	private static void usage1(String[] args) {
		int n = Integer.parseInt(args[0]);
		int d = Integer.parseInt(args[1]);
		int k = Integer.parseInt(args[2]);
		int m = Integer.parseInt(args[3]);
		double p = Double.parseDouble(args[4]);

		double density = (m * 2) / (double) (n * (n - 1));
		double exponent = -2 / ((n - 1) * density);
		double pcrit = (1 - Math.pow(d, exponent));
		System.out.println("\nProsser Smith prediction pcrit = " + pcrit + "  (nbAllowedTuples=" + Math.round((1 - pcrit) * Math.pow(d, k))
				+ ",nbDisallowedTuples=" + Math.round(pcrit * Math.pow(d, k)) + ")");

		double alpha = Math.log(d) / Math.log(n);
		System.out.println("\nalpha = " + alpha + " n^alpha = " + Math.pow(n, alpha));
		double r = m / (n * Math.log(n));
		System.out.println("r = " + r + " r*n^log(n) = " + r * n * Math.log(n));

		boolean condition1 = (alpha > 1 / (double) k);
		boolean conditionTheorem1 = (k >= (1 / (1 - p)));
		boolean conditionTheorem2 = (k * Math.exp(-alpha / r) >= 1);
		boolean validTheorem1 = condition1 && (0 < p && p < 1) && conditionTheorem1;
		boolean validTheorem2 = condition1 && (r > 0) && conditionTheorem2;

		System.out.println("\nTheorem 1 is " + (validTheorem1 ? "valid" : "not valid") + " as alpha > 1/k : " + condition1 + ", 0 < p < 1 : " + (0 < p && p < 1)
				+ ", k>=(1/(1-p)) : " + conditionTheorem1);
		double rcrit = -alpha / Math.log(1 - p);
		System.out.println("  => rcrit = " + rcrit + (validTheorem1 ? "" : " NOT VALIDATING theorem 1"));

		System.out.println("\nTheorem 2 is " + (validTheorem2 ? "valid" : "not valid") + " as alpha > 1/k : " + condition1 + ", r > 0 : " + (r > 0)
				+ ", ke^(-alpha/r)=" + k * Math.exp(-alpha / r) + " >= 1 : " + conditionTheorem2);

		pcrit = 1 - Math.exp(-alpha / r);
		System.out.println("  => pcrit = " + pcrit + (validTheorem2 ? "" : " NOT VALIDATING theorem 2"));
		if (args.length == 6) {
			int nbNextSteps = Integer.parseInt(args[5]);
			for (int i = 1; i <= nbNextSteps; i++)
				System.out.println("  => n = " + (n + i) + " d = " + Math.pow(n + i, alpha) + " m = " + r * (n + i) * Math.log(n + i));
		}
	}

	private static void usage2(String[] args) {
		int n = Integer.parseInt(args[0]);
		double alpha = Double.parseDouble(args[1]);
		double r = Double.parseDouble(args[2]);
		double d = Math.pow(n, alpha);
		double m = r * n * Math.log(n);
		System.out.println("d (domain size) = " + d + " m (number of constraints) = " + m);
		double pcrit = 1 - Math.exp(-alpha / r);
		System.out.println("  => pcrit = " + pcrit);
	}

	public static void main(String[] args) {
		if (args.length >= 5)
			usage1(args);
		else if (args.length == 3)
			usage2(args);
		else {
			System.out.println("usage 1  java " + Thresholds.class.getName() + " <nVariables> <domainSize> <arity> <nConstraints> <tightness> {<nNextSteps>}");
			System.out.println("usage 2 : java " + Thresholds.class.getName() + " <nVariables> <alpha> <r> {<k>}");
		}
	}
}