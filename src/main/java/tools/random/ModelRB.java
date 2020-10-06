/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package tools.random;

import org.xcsp.common.Utilities;

import dashboard.Arguments;
import executables.Resolution;
import problems.rand.ExplicitRandomQuestion;
import utility.Kit;

public class ModelRB {

	private static boolean respectCondition1(int k, double alpha) {
		return (alpha > 1 / (double) k);
	}

	private static boolean respectCondition2(int k, double alpha, double r) {
		return (k * Math.exp(-alpha / r) >= 1);
	}

	private static void manageThreshod(double alpha, double r) {
		System.out.println("\t The threshold value is pcrit = " + (1 - Math.exp(-alpha / r)));
	}

	private static void manageTheorem2(int k, double alpha, double r) {
		if (respectCondition1(k, alpha) && respectCondition2(k, alpha, r)) {
			System.out.println("\t Theorem 2 is valid");
			System.out.println("\t  - as alpha = " + alpha + " is strictly greater than 1/k = " + (1 / (double) k));
			System.out.println("\t  - as ke^(-alpha/r) = " + (k * Math.exp(-alpha / r)) + " is greater than or equal to 1");
		} else {
			System.out.println("\t Theorem 2 is not valid");
			if (!respectCondition1(k, alpha))
				System.out.println("\t  - as alpha = " + alpha + " is not strictly greater than 1/k = " + (1 / (double) k));
			if (!respectCondition2(k, alpha, r))
				System.out.println("\t  - as ke^(-alpha/r) = " + (k * Math.exp(-alpha / r)) + " is not greater than or equal to 1");
		}
	}

	private static void usage0(String[] args) {
		int k = Utilities.toInteger(args[0], v -> v >= 2);
		double alpha = Utilities.toDouble(args[1]), r = Utilities.toDouble(args[2]);
		Kit.control(alpha > 0 && r > 0);
		manageThreshod(alpha, r);
		manageTheorem2(k, alpha, r);
	}

	private static void usage1(String[] args) {
		int k = Utilities.toInteger(args[0], v -> v >= 2);
		int n = Utilities.toInteger(args[1], v -> v >= 2);
		double alpha = Utilities.toDouble(args[2]);
		double r = Utilities.toDouble(args[3]);
		manageThreshod(alpha, r);
		manageTheorem2(k, alpha, r);
		int d = (int) Math.round(Math.pow(n, alpha));
		int m = (int) Math.round(r * n * Math.log(n));
		double realAlpha = Math.log(d) / Math.log(n);
		double realR = m / (n * Math.log(n));
		double realCrit = 1 - Math.pow(Math.E, -realAlpha / realR);
		System.out.println("\t Rounding values gives:");
		System.out.println("\t -  the domain size d  = " + d + " (alpha = " + realAlpha + ")");
		System.out.println("\t  - the number of constraints m = " + m + "(r = " + realR + ")");
		System.out.println("\t  - the threshold value pcrit = " + realCrit);
	}

	private static void usage2(String[] args) {
		int k = Utilities.toInteger(args[0], v -> v >= 2);
		int n = Utilities.toInteger(args[1], v -> v >= 2);
		int d = Utilities.toInteger(args[2], v -> v >= 2);
		int m = Utilities.toInteger(args[3], v -> v >= 2);
		double alpha = Math.log(d) / Math.log(n);
		double r = m / (n * Math.log(n));
		System.out.println("\t We have:");
		System.out.println("\t -  alpha = " + alpha);
		System.out.println("\t -  r = " + r);
		manageThreshod(alpha, r);
		manageTheorem2(k, alpha, r);
	}

	private static void usage3(String[] args) {
		int k = Utilities.toInteger(args[0], v -> v >= 2);
		int n = Utilities.toInteger(args[1], v -> v >= 2);
		double alpha = Utilities.toDouble(args[2]), r = Utilities.toDouble(args[3]);
		int d = (int) Math.round(Math.pow(n, alpha));
		int e = (int) Math.round(r * n * Math.log(n));
		double realAlpha = Math.log(d) / Math.log(n);
		double realR = e / (n * Math.log(n));
		double realCrit = 1 - Math.pow(Math.E, -realAlpha / realR);
		int roundedRealCrit = (int) Math.round(realCrit * 1000);
		int delta = Utilities.toInteger(args[4]);
		int t = roundedRealCrit + delta;
		Kit.control(t >= 0 && t <= 1000, () -> "parameter should be between 0 and 1000");
		boolean forced = Utilities.toBoolean(args[5]);
		boolean merged = Utilities.toBoolean(args[6]);
		int seed = Utilities.toInteger(args[7], v -> v >= 0);
		int nbInstances = Utilities.toInteger(args[8], v -> v >= 1);
		String s = nbInstances + " " + ExplicitRandomQuestion.class.getName() + " " + n + " " + d + " " + e + " " + k + " 1 " + (t / 1000.0) + " " + seed
				+ " 0  0 " + (merged ? "n" : "y") + " " + (forced ? "y" : "n") + " n 0 -export=file";
		System.out.println("Command : " + s);
		Arguments.loadArguments(s.split("\\s+"));
		(new Resolution()).start();
	}

	public static void main(String[] args) {
		if (args.length == 3)
			usage0(args);
		else if (args.length == 4)
			usage1(args);
		else if (args.length == 5)
			usage2(args);
		else if (args.length == 9)
			usage3(args);
		else {
			System.out.println("GeneratorRB 2.0");
			System.out.println("usage 0: java " + ModelRB.class.getName() + " <arity> <alpha> <r>");
			System.out.println("usage 1: java " + ModelRB.class.getName() + " <arity> <nVariables> <alpha> <r>");
			System.out.println("usage 2: java " + ModelRB.class.getName() + " <arity> <nVariables> <domainSize> <nConstraints> <tightness>");
			System.out.println("usage 3: java " + ModelRB.class.getName() + " <arity> <nVariables> <alpha> <r> <delta> <forced> <merged> <seed> <nInstances>");
		}
	}
}