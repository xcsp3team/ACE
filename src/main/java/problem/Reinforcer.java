package problem;

import static java.util.stream.Collectors.joining;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.TreeSet;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import sets.SetSparse;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Domain;
import variables.Variable;
import variables.Variable.VariableInteger;

/**
 * These classes are useful to reinforce a constraint network by adding either redundant constraints or symmetry-breaking constraints.
 * 
 * @author Christophe Lecoutre
 */
public class Reinforcer {

	/**
	 * Class for inferring AllDifferent constraints
	 */
	public static final class ReinforcerAllDifferent {

		public static final String N_CLIQUES = "nCliques";

		private static int[][] computeIrreflexiveNeigbours(List<Variable> variables, List<Constraint> constraints) {
			Set<Integer>[] variableNeighbours = variables.stream().map(x -> new TreeSet<>()).toArray(TreeSet[]::new);
			for (Constraint c : constraints)
				if (c.scp.length == 2 && c.isIrreflexive()) {
					variableNeighbours[c.scp[0].num].add(c.scp[1].num);
					variableNeighbours[c.scp[1].num].add(c.scp[0].num);
				}
			return Kit.intArray2D(variableNeighbours);
		}

		private static int countNeighboursAtLevel(int[] neighbours, int level, int[] levels) {
			int cnt = 0;
			for (int j : neighbours)
				if (levels[j] == level)
					cnt++;
			return cnt;
		}

		private static boolean controlClique(Variable[] scp, List<Constraint> constraints) {
			for (int i = 0; i < scp.length; i++)
				for (int j = i + 1; j < scp.length; j++) {
					Variable x = scp[i], y = scp[j];
					Kit.control(constraints.stream().anyMatch(c -> c.isIrreflexive() && c.involves(x, y)), "pb clique with " + x + " " + y);
				}
			return true;
		}

		/**
		 * Builds and returns a list of cliques (irreflexive pairwise variables) from the specified array of variables with respect to the specified list of
		 * constraints. Each such clique can be used to build an AllDifferent constraint. The two last parameters are used to control the number and the size of
		 * the cliques.
		 * 
		 * @param variables
		 *            a list of variables
		 * @param constraints
		 *            a list of constraints
		 * @param nLimit
		 *            the maximum number of cliques to find
		 * @param sLimit
		 *            the minimum size of cliques to be taken into account
		 * @return a list of cliques (irreflexive pairwise variables) from the specified array of variables with respect to the specified list of constraints
		 */
		public static List<Variable[]> buildCliques(List<Variable> variables, List<Constraint> constraints, int nLimit, int sLimit) {
			int[][] variableNeighbours = computeIrreflexiveNeigbours(variables, constraints);
			int[] degrees = Stream.of(variableNeighbours).mapToInt(t -> t.length).toArray();
			int[] levels = new int[variables.size()];
			int[] clique = new int[variables.size()]; // an array to store the current clique
			SetSparse set = new SetSparse(variables.size(), true);
			List<Variable[]> cliques = new ArrayList<>();
			for (int k = 1; k <= nLimit; k++) {
				// we build the kth clique
				int level = 0, cliqueSize = 0;
				int num = -1;
				for (int i = 0; i <= set.limit; i++)
					if (num == -1 || degrees[set.dense[i]] > degrees[num])
						num = set.dense[i];
				while (num != -1) {
					levels[num] = -k; // we put num in the current clique (k)
					clique[cliqueSize++] = num;
					set.remove(num);
					int[] neighbours = variableNeighbours[num];
					for (int j : neighbours)
						if (levels[j] == level)
							levels[j] = level + 1; // we keep them for the rest of the selection process
					level += 1;
					for (int j : neighbours)
						if (levels[j] == level)
							degrees[j] = countNeighboursAtLevel(variableNeighbours[j], level, levels);
					num = -1;
					for (int j : neighbours)
						if (levels[j] == level && (num == -1 || degrees[j] > degrees[num]))
							num = j;
				}
				for (int i = 0; i <= set.limit; i++)
					levels[set.dense[i]] = 0;
				// System.out.println("cliqueSize " + cliqueSize);
				if (cliqueSize <= sLimit)
					break;
				VariableInteger[] scp = IntStream.range(0, cliqueSize).mapToObj(i -> variables.get(clique[i])).sorted().toArray(VariableInteger[]::new);
				cliques.add(scp);
				System.out.println(" clique " + k + " of size " + scp.length + " {" + Kit.join(scp) + "}");
				assert controlClique(scp, constraints);
				for (int i = 0; i <= set.limit; i++)
					degrees[set.dense[i]] = countNeighboursAtLevel(variableNeighbours[set.dense[i]], 0, levels); // reinitialization of degrees
			}
			return cliques;
		}
	}

	/**
	 * Class for inferring symmetry-breaking constraints
	 */
	public static final class ReinforcerAutomorphism {

		public static final String N_GENERATORS = "nGenerators";
		public static final String SYMMETRY_WALL_CLOCK_TIME = "symmetryWckTime";

		public static Stopwatch stopwatch;

		private static int nCurrentColors;

		private static class Node {
			private int id;
			private int color;
			private int[] neighbors;

			private Node(int id, int color, int[] neighbors) {
				this.id = id;
				this.color = color;
				this.neighbors = neighbors;
			}

			private Node(int id, int color) {
				this(id, color, new int[0]);
			}

			@Override
			public String toString() {
				return "node " + (id + 1) + " color=" + color + " neighbors=" + IntStream.of(neighbors).mapToObj(v -> (v + 1) + " ").collect(joining());
			}
		}

		private static void addColorNode(Map<Integer, List<Integer>> groupsOfColors, int id, int color) {
			groupsOfColors.computeIfAbsent(color, k -> new ArrayList<>()).add(id);
		}

		private static String manageDomainKeyOf(Map<String, Domain> mapOfModifiedDomains, Domain dom) {
			if (dom.nRemoved() == 0)
				return dom.typeName() + "0";
			for (int i = 1; true; i++) {
				String key = dom.typeName() + i;
				Domain d = mapOfModifiedDomains.get(key);
				if (d == null) {
					mapOfModifiedDomains.put(key, d);
					return key;
				} else if (dom.size() == d.size()) {
					boolean equal = true;
					for (int a = dom.first(); equal && a != -1; a = dom.next(a))
						if (!d.contains(a))
							equal = false;
					if (equal)
						return key;
				}
			}
		}

		private static int[] buildVariableNodes(Map<Integer, List<Integer>> groupsOfColors, List<Variable> vars) {
			nCurrentColors = 0;
			Map<String, Variable> mapOfDomainColors = new HashMap<>();
			Map<String, Domain> mapOfModifiedDomains = new HashMap<>();
			int[] variableNodes = new int[vars.size()]; // 1D = variable id ; value = color id
			for (int i = 0; i < variableNodes.length; i++) {
				String key = manageDomainKeyOf(mapOfModifiedDomains, vars.get(i).dom);
				Variable x = mapOfDomainColors.get(key);
				if (x == null) {
					mapOfDomainColors.put(key, vars.get(i));
					variableNodes[i] = nCurrentColors++;
				} else
					variableNodes[i] = variableNodes[x.num];
				addColorNode(groupsOfColors, i, variableNodes[i]);
			}
			return variableNodes;
		}

		private static List<Node> buildConstraintNodes(Map<Integer, List<Integer>> groupsOfColors, Collection<Constraint> ctrs, int nVariables) {
			Map<String, int[]> mapOfRelationColors = new HashMap<>();
			List<Node> constraintNodes = new ArrayList<>();
			int nNodes = nVariables; // because nodes for variables already built (one node per variable)
			for (Constraint c : ctrs) {
				Variable[] scope = c.scp;
				String key = c.getKey(); // TODO : pb with key null for pb HSP
				int[] t = mapOfRelationColors.get(key);
				if (t == null) {
					int[] symmetryMatching = c.symmetryMatching();
					t = new int[scope.length + 1];
					if (symmetryMatching != null) {
						t[t.length - 1] = nCurrentColors++;
						int max = 0;
						for (int i = 0; i < symmetryMatching.length; i++) {
							if (symmetryMatching[i] > max)
								max = symmetryMatching[i];
							t[i] = nCurrentColors + (symmetryMatching[i] - 1);
						}
						nCurrentColors += max;
					} else {
						for (int i = 0; i < t.length; i++)
							t[i] = nCurrentColors++;
					}
					mapOfRelationColors.put(key, t);
				}
				int v = nNodes;
				constraintNodes.add(new Node(nNodes, t[t.length - 1]));
				addColorNode(groupsOfColors, nNodes++, t[t.length - 1]);
				for (int i = 0; i < t.length - 1; i++) {
					constraintNodes.add(new Node(nNodes, t[i], new int[] { scope[i].num, v }));
					addColorNode(groupsOfColors, nNodes++, t[i]);
				}
			}
			return constraintNodes;
		}

		private static void buildGAPEdges(PrintWriter out, List<Node> constraintNodes) {
			out.print('[');
			Iterator<Node> it = constraintNodes.iterator();
			while (it.hasNext()) {
				Node node = it.next();
				for (int i = 0; i < node.neighbors.length; i++) {
					out.print('[');
					out.print(node.id + 1);
					out.print(',');
					out.print(node.neighbors[i] + 1);
					out.print(']');
					if (it.hasNext() || i < node.neighbors.length - 1)
						out.print(',');
				}
			}
			out.print(']');
		}

		private static void buildGAPGroups(PrintWriter out, Map<Integer, List<Integer>> groupsOfColors) {
			out.print('[');
			boolean first = true;
			for (List<Integer> list : groupsOfColors.values()) {
				if (first)
					first = false;
				else
					out.print(',');
				out.print('[');
				for (int i = 0; i < list.size(); i++) {
					out.print(list.get(i) + 1);
					if (i < list.size() - 1)
						out.print(',');
				}
				out.print(']');
			}
			out.print(']');
		}

		private static String saveInGAPFormat(Map<Integer, List<Integer>> groupsOfColors, List<Node> constraintNodes, int nNodes) {
			String graphFilename = "graph" + new Random().nextInt() + ".gap";
			try (PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(graphFilename)))) {
				out.print("AutGroupGraph(UnderlyingGraph(EdgeOrbitsGraph( Group(()),");
				buildGAPEdges(out, constraintNodes);
				out.print(',');
				out.print(nNodes);
				out.print(")),");
				buildGAPGroups(out, groupsOfColors);
				out.println(");");
			} catch (Exception e) {
				Kit.exit(e);
			}
			return graphFilename;
		}

		private static List<int[]> parseGenerator(String line, int nVariables) {
			List<int[]> list = new ArrayList<>();
			StringTokenizer st1 = new StringTokenizer(line, "()");
			while (st1.hasMoreTokens()) {
				String cycle = st1.nextToken();
				StringTokenizer st2 = new StringTokenizer(cycle, ",");
				if (!st2.hasMoreTokens())
					break;
				int id = Integer.parseInt(st2.nextToken()) - 1;
				if (id >= nVariables)
					break;
				int[] t = new int[st2.countTokens() + 1];
				t[0] = id;
				for (int i = 1; i < t.length; i++)
					t[i] = Integer.parseInt(st2.nextToken()) - 1;
				list.add(t);
			}
			return list;
		}

		private static List<List<int[]>> runSaucy(String filename, int nVariables) {
			List<List<int[]>> generators = new ArrayList<>();
			String cmd = System.getenv("HOME") + File.separator + "tools" + File.separator + "saucy-1.1" + File.separator + "saucy -t 20 -g " + filename;
			Kit.log.info("Command for symmetry breaking is " + cmd);
			Process p = null;
			try {
				p = Runtime.getRuntime().exec(cmd);
			} catch (IOException e) {
				e.printStackTrace();
			}
			if (p != null)
				try (BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
					in.readLine();
					String line = in.readLine().trim();
					while (!line.equals("]")) {
						List<int[]> generator = parseGenerator(line, nVariables);
						if (generator.size() > 0) // {
							generators.add(generator); // break; }
						// else System.out.println(" not exploitable generator : " + line);
						line = in.readLine();
					}
					in.close();
					p.waitFor();
					p.destroy();
					// Runtime.getRuntime().exec("rm " + graphFileName);
				} catch (Exception e) {
					e.printStackTrace();
				}
			return generators;
		}

		private static void displayGenerators(List<List<int[]>> generators) {
			for (List<int[]> generator : generators)
				System.out.println("generator = " + generator.stream().map(t -> "[ " + Kit.join(t) + " ]").collect(joining()));
		}

		private static void displayGraph(int[] variableNodes, List<Node> constraintNodes) {
			System.out.println("variableNodes");
			for (int i = 0; i < variableNodes.length; i++)
				System.out.println((i + 1) + ":" + variableNodes[i]);
			System.out.println("constraintNodes");
			for (int i = 0; i < constraintNodes.size(); i++)
				System.out.println((i + 1) + ":" + constraintNodes.get(i));
		}

		/**
		 * Builds and returns a list of generators (based on a computed automorphism group) from the specified array of variables with respect to the specified
		 * list of constraints. Each such generator can be used to build a symmetry-breaking constraint.
		 * 
		 * @param variables
		 *            an array of variables
		 * @param constraints
		 *            a list of constraints
		 * @return a list of generators (based on a computed automorphism group) from the specified array of variables with respect to the specified list of
		 *         constraints
		 */
		public static List<List<int[]>> buildGenerators(List<Variable> variables, List<Constraint> constraints) {
			stopwatch = new Stopwatch();
			Map<Integer, List<Integer>> groupsOfColors = new HashMap<>(); // 1D = color number ; value = list of node ids with this color
			int[] variableNodes = buildVariableNodes(groupsOfColors, variables);
			List<Node> constraintNodes = buildConstraintNodes(groupsOfColors, constraints, variables.size());
			String graphFilename = saveInGAPFormat(groupsOfColors, constraintNodes, variableNodes.length + constraintNodes.size());
			List<List<int[]>> generators = runSaucy(graphFilename, variables.size());
			if (variables.get(0).problem.head.control.general.verbose > 0)
				displayGenerators(generators);
			// displayGraph(variableNodes,constraintNodes);
			return generators;
		}
	}

}
