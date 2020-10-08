/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package tools.output;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Scanner;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import constraints.Constraint;
import constraints.CtrHard;
import problem.Problem;
import search.backtrack.DecisionRecorder;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;

public class Graphviz {

	static enum GraphType {
		INTER, PRIMAL, CONSTRAINT, COMPATIBILITY, DECISIONS;
	}

	static enum FilterType {
		DOT, NEATO, TWOPI, CIRCO, FDP;
	}

	private final static String EMPTY_LABEL = " [label=\"\",width=.4,height=.4,fillcolor=lightblue,style=filled] ;";

	private static String GREEN = "green2", RED = "red", GREY = "grey90";
	private static String[] BLUES = { "aquamarine2", "aquamarine4", "blue2", "blue4", "cyan2", "cyan4", "purple1", "purple4", "royalblue1", "royalblue3" };

	private static GraphType graphType = GraphType.PRIMAL; // CONSTRAINT;
	// neato -Tpdf scen11-f6-3.dot -o scen11-f6-3.pdf
	private static FilterType filterType = FilterType.NEATO;

	private static int countdown = 1;
	private static boolean displayAll = true;
	private static boolean automaticSave = true;
	private static int automaticIncrementCountdown = 1;
	private static int automaticCnt = 0;

	private static int[] variableIndices;

	private static String computeColorFrom(long weight) {
		if (weight == 0)
			return "\"#FFFFFF\"" + ",color=white";
		if (weight > 255)
			return "\"#0000FF\"";
		weight = 255 - weight;
		String convertion = Long.toHexString(weight);
		String s = weight > 255 ? "FF" : weight < 15 ? "0" + convertion : convertion;
		return "\"#" + s + s + "FF\"";
	}

	private static long computeWeightColorOf(Variable x) {
		return (int) x.wdeg() - x.deg();
	}

	private static void constraintGraph(Problem pb, PrintWriter out) {
		Kit.control(Stream.of(pb.constraints).allMatch(c -> c.scp.length == 2), () -> "Must be applied on binary CNs");
		boolean weightVisualisation = false; // true;
		out.println("graph G {");
		out.println("rankdir=TB ;");
		out.println("ranksep=1 ;");
		for (Variable x : pb.variables) {
			if (x.isAssigned() && !displayAll)
				continue;
			if (weightVisualisation)
				out.println("  " + x.defaultId() + " [style=filled,fillcolor=" + computeColorFrom(computeWeightColorOf(x)) + "] ;");
			else
				out.println("  " + x.defaultId() + " [style=filled,fillcolor="
						+ (x.isAssigned() ? GREEN + ",label=\"" + x + "=" + x.dom.uniqueValue() + "\"" : "white") + "] ;");
		}
		for (Constraint c : pb.constraints) {
			Variable x = c.scp[0].num < c.scp[1].num ? c.scp[0] : c.scp[1], y = c.scp[0] == x ? c.scp[1] : c.scp[0];
			String edge = "  " + x.defaultId() + " -- " + y.defaultId();
			// if (weightVisualisation || constraint.getNbPastVariables() == 0) {
			if (weightVisualisation && computeWeightColorOf(x) == 0 && computeWeightColorOf(y) == 0)
				out.println(edge + "[color=white,fillcolor=white];");
			else
				out.println(edge + ";");
			// } else if (displayAll) out.println(edge + "[style=invis] ;"); // dotted] ;");
		}
		out.println("}");
	}

	private static boolean isSelectedVariable(Variable x) {
		return variableIndices == null || IntStream.of(variableIndices).anyMatch(num -> num == x.num);
	}

	private static void interGraph(Problem pb, PrintWriter out) {
		out.println("graph G {");
		out.println("compound=true ;");
		// out.println("rankdir=BT ;");
		out.println("ranksep=1 ;");
		for (Variable x : pb.variables) {
			if (!isSelectedVariable(x))
				continue;
			out.println("subgraph cluster" + x.num + " {");
			out.println("label=" + x);
			out.println("labeljust=l");
			out.println("style=filled");
			out.println("color=" + GREY);
			if (variableIndices != null) {
				for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
					out.println("  " + x + "_" + a + " [label=" + a + ",style=filled,fillcolor=lightblue] ;");
			} else
				for (int a = 0; a < x.dom.initSize(); a++) {
					String node = "  " + x + "_" + a + " [label=" + a + ",style=filled,fillcolor=";
					if (x.dom.isPresent(a))
						out.println(node + (x.isAssigned() ? GREEN : "white") + "] ;");
					else if (displayAll)
						out.println(node + (x.dom.isRemovedAtLevel(a, 0) ? RED : "orange") + "] ;");
				}
			out.println("}");
		}
		if (variableIndices != null) {
			for (int i = 0; i < variableIndices.length; i++) {
				Variable x = pb.variables[variableIndices[i]];
				for (int j = i + 1; j < variableIndices.length; j++) {
					Variable y = pb.variables[variableIndices[j]];
					if (x.isNeighbourOf(y)) {
						String s1 = "cluster" + x.num, s2 = "cluster" + y.num;
						out.println(" " + x + "_" + x.dom.first() + " -- " + y + "_" + y.dom.first() + " [ltail=" + s1 + ",lhead=" + s2 + "] ;");
					}
				}
			}

		} else
			for (int i = 0; i < pb.variables.length; i++)
				for (int j = i + 1; j < pb.variables.length; j++)
					if (pb.variables[i].isNeighbourOf(pb.variables[j])) {
						String s1 = "cluster" + pb.variables[i].num, s2 = "cluster" + pb.variables[j].num;
						out.println(" " + pb.variables[i] + "_" + 0 + " -- " + pb.variables[j] + "_" + 0 + " [ltail=" + s1 + ",lhead=" + s2 + "] ;");
					}
		out.println("}");
	}

	private static void primalGraph(Problem pb, PrintWriter out) {
		boolean weightVisualisation = false; // true;
		out.println("graph G {");
		out.println("rankdir=TB ;");
		out.println("ranksep=1 ;");
		for (Variable x : pb.variables) {
			System.out.println(x);
			if (x.isAssigned() && !displayAll)
				continue;
			if (weightVisualisation) {
				out.println("  " + x.defaultId() + " [style=filled,fillcolor=" + computeColorFrom((int) x.wdeg() - x.deg()) + "] ;");
			} else
				out.println("  " + x.defaultId() + " [style=filled,fillcolor="
						+ (x.isAssigned() ? GREEN + ",label=\"" + x.defaultId() + "=" + x.dom.uniqueValue() + "\"" : "white") + "] ;");
		}
		for (Constraint c : pb.constraints) {
			for (int i = 0; i < c.scp.length - 1; i++) {
				for (int j = i + 1; j < c.scp.length; j++) {
					Variable x = c.scp[i].num < c.scp[j].num ? c.scp[i] : c.scp[j];
					Variable y = c.scp[i] == x ? c.scp[j] : c.scp[i];
					String edge = "  " + x.defaultId() + " -- " + y.defaultId();
					if (weightVisualisation || c.futvars.size() == c.scp.length)
						out.println(edge + ";");
					else if (displayAll)
						out.println(edge + "[style=invis] ;"); // dotted] ;");
				}
			}
		}
		out.println("}");
	}

	private static String varName(Problem pb, Variable x) {
		return pb.variables.length > 6 ? x.toString()
				: pb.variables.length == 2 ? (x.num == 0 ? "x" : "y") : "" + ((char) (((short) 'z') - (pb.variables.length - x.num - 1)));
	}

	private static void compatibilityGraph(Problem pb, PrintWriter out) {
		Kit.control(Stream.of(pb.constraints).allMatch(c -> c.scp.length == 2), () -> "Must be applied on binary CNs");
		// TODO faire version arite quelconque avec hyperate obtenue a partir de noeuds suppelemntaires (chauqe tuple = 1 noeud supplementaire)
		out.println("graph G {");
		// out.println("rankdir=LR ;");
		out.println("ranksep=1 ;");
		for (Variable x : pb.variables) {
			out.println("subgraph cluster" + x.num + " {");
			out.println("label=" + varName(pb, x));
			out.println("labeljust=l");
			out.println("style=filled");
			out.println("color=" + GREY);
			for (int a = 0; a < x.dom.initSize(); a++) {
				String node = "  " + varName(pb, x) + "_" + a + " [label=" + a + ",style=filled,fillcolor=";
				if (x.dom.isPresent(a))
					out.println(node + (x.isAssigned() ? GREEN : "white") + "] ;");
				else if (displayAll) {
					// out.println(node + (elements.getAbsentLevelOf(index) == 0 ? "red" : "red") + "] ;");
					node = "  " + varName(pb, x) + "_" + a + " [label=" + a + ",style=dotted,fillcolor=";
					// above A VIRER SI PAS DOTTED
					out.println(node + (x.dom.isRemovedAtLevel(a, 0) ? RED : "orange") + "] ;");
				}
			}
			out.println("}");
		}
		int cnt = 0;
		for (Constraint c : pb.constraints) {
			if (c.futvars.size() != c.scp.length && !displayAll)
				continue;
			if (!(c instanceof CtrHard))
				continue;
			cnt++;
			Variable x = c.scp[0], y = c.scp[1];
			for (int a = 0; a < x.dom.initSize(); a++) {
				for (int b = 0; b < y.dom.initSize(); b++) {
					if (((CtrHard) c).seekFirstSupportWith(0, a, 1, b)) {
						String edge = "  " + varName(pb, x) + "_" + a + " -- " + varName(pb, y) + "_" + b;
						if (x.dom.isPresent(a) && y.dom.isPresent(b))
							out.println(edge + (pb.constraints.length < BLUES.length ? " [color=" + BLUES[cnt] + "]  " : "") + ";");
						else if (displayAll)
							out.println(edge + " [style=dotted]" + " ;");
					}
				}
			}
		}
		out.println("}");
	}

	private static void recordDecisions(Problem pb, PrintWriter out) {
		DecisionRecorder dr = ((SolverBacktrack) (pb.solver)).dr;
		out.println("digraph G {");
		out.println("rankdir=TB ;");
		// out.println("ranksep=1 ;");
		String previousNode = "root";
		out.println(previousNode + EMPTY_LABEL);
		for (int i = dr.decisions.limit; i >= 0; i--) {
			int dec = dr.decisions.dense[i];
			Variable x = dr.varIn(dec);
			int a = dr.idxIn(dec);
			String currentNode = x.toString() + a;
			String positiveLabel = "\" " + x + " = " + a + "\"";
			if (dec < 0) {
				String currentNodeBis = currentNode + "bis";
				if (dr.isFailedAssignment(i))
					out.println(currentNodeBis + " [shape=plaintext,fontcolor=red,fontname=Helvetica,label=\"X\",fontsize=20] ;");
				else
					out.println(currentNodeBis + " [shape=triangle,fillcolor=orangered,style=filled,labelfloat=true,label=\"...\",width=.6,height=.6] ;");
				out.println("  " + previousNode + " -> " + currentNodeBis + " [label=" + positiveLabel + ",fontsize=12] ;");
				out.println(currentNode + EMPTY_LABEL);
				String negativeLabel = "\" " + x + " != " + a + "\"";
				out.println("  " + previousNode + " -> " + currentNode + " [label=" + negativeLabel + ",fontsize=12] ;");
			} else {
				out.println(currentNode + EMPTY_LABEL);
				out.println("  " + previousNode + " -> " + currentNode + " [label=" + positiveLabel + ",fontsize=12] ;");
			}
			previousNode = currentNode;
		}
		out.println("}");
	}

	public static void saveGraph(Problem pb, String patternForSaving) {
		if (patternForSaving.equals(Constants.EMPTY_STRING))
			return;
		// Kit.control(patternSaving.m 3 bits
		if (--countdown != 0)
			return;
		// System.out.println((char) (((short) 'z') - 1));
		String prefix = "toto";
		String dotFileName = prefix + ".dot";
		try (PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(dotFileName)))) {
			if (graphType == GraphType.INTER)
				interGraph(pb, out);
			else if (graphType == GraphType.PRIMAL)
				primalGraph(pb, out);
			else if (graphType == GraphType.CONSTRAINT)
				constraintGraph(pb, out);
			else if (graphType == GraphType.COMPATIBILITY)
				compatibilityGraph(pb, out);
			else if (graphType == GraphType.DECISIONS)
				recordDecisions(pb, out);

			String epsFileName = prefix + ".eps";
			String command = filterType.toString().toLowerCase() + " -Tps " + dotFileName + " -o " + epsFileName;
			Process p = Runtime.getRuntime().exec(command);
			System.out.println("waiting for command: " + command);
			p.waitFor();
			p.exitValue();
			command = "epstopdf " + epsFileName;
			p = Runtime.getRuntime().exec(command);
			// System.out.println("waiting for command " + command);
			p.waitFor();
			p.exitValue();
			// p.destroy();
		} catch (Exception e) {
			e.printStackTrace();
		}
		if (!automaticSave) {
			System.out.print("waiting...");
			try (Scanner scanner = new Scanner(System.in)) {
				String s = scanner.nextLine().trim();
				countdown = s.equals("") ? 1 : Integer.parseInt(s);
			} catch (Exception e) {
				e.printStackTrace();
			}
		} else
			countdown = automaticIncrementCountdown;
	}
}
