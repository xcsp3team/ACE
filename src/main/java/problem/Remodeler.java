package problem;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
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
import constraints.global.Lexicographic.LexicographicLE;
import constraints.intension.Intension;
import sets.SetSparse;
import utility.Enums.ESymmetryBreaking;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Domain;
import variables.Variable;
import variables.Variable.VariableInteger;

public class Remodeler {

	/*************************************************************************
	 ***** Interfaces
	 *************************************************************************/

	public static final class DeducingAllDifferent {
		public static final String N_CLIQUES = "nCliques";

		private Problem problem;

		public int nBuiltCliques;

		private int[][] computeIrreflexivesNeigbours(Variable[] variables, List<Constraint> constraints) {
			Set<Integer>[] neighbours = Stream.of(variables).map(x -> new TreeSet<>()).toArray(TreeSet[]::new);
			for (Constraint c : constraints)
				if (c.scp.length == 2 && c.isIrreflexive()) {
					neighbours[c.scp[0].num].add(c.scp[1].num);
					neighbours[c.scp[1].num].add(c.scp[0].num);
				}
			return Kit.intArray2D(neighbours);
		}

		private int countNeighboursAtLevel(int[] neighbours, int level, int[] levels) {
			int cnt = 0;
			for (int j : neighbours)
				if (levels[j] == level)
					cnt++;
			return cnt;
		}

		private List<VariableInteger[]> buildCliques(Variable[] variables, List<Constraint> constraints, int nLimit, int sLimit) {
			int n = variables.length;
			int[][] allNeighbours = computeIrreflexivesNeigbours(variables, constraints);
			int[] degrees = Stream.of(allNeighbours).mapToInt(t -> t.length).toArray();
			int[] levels = new int[n];
			int[] tmp = new int[n];
			SetSparse set = new SetSparse(n, true);
			List<VariableInteger[]> list = new ArrayList<>();
			for (int k = 1; k <= nLimit; k++) {
				// we build the clique
				int level = 0, cliqueSize = 0;
				int num = -1;
				for (int i = 0; i <= set.limit; i++)
					if (num == -1 || degrees[set.dense[i]] > degrees[num])
						num = set.dense[i];
				while (num != -1) {
					levels[num] = -k; // we put num in the current clique (k)
					tmp[cliqueSize++] = num;
					set.remove(num);
					int[] neighbours = allNeighbours[num];
					for (int j : neighbours)
						if (levels[j] == level)
							levels[j] = level + 1; // we keep them for the rest of the selection process
					level += 1;
					for (int j : neighbours)
						if (levels[j] == level)
							degrees[j] = countNeighboursAtLevel(allNeighbours[j], level, levels);
					num = -1;
					for (int j : neighbours)
						if (levels[j] == level && (num == -1 || degrees[j] > degrees[num]))
							num = j;
				}
				for (int i = 0; i <= set.limit; i++)
					levels[set.dense[i]] = 0;

				if (cliqueSize <= sLimit)
					break;
				VariableInteger[] scp = IntStream.range(0, cliqueSize).mapToObj(i -> problem.variables[tmp[i]]).sorted().toArray(VariableInteger[]::new);
				list.add(scp);
				display(k, scp);
				assert controlClique(scp, constraints);
				for (int i = 0; i <= set.limit; i++)
					degrees[set.dense[i]] = countNeighboursAtLevel(allNeighbours[set.dense[i]], 0, levels); // reinitialization of degrees
			}
			return list;
		}

		public DeducingAllDifferent(Problem problem) {
			this.problem = problem;
			int nLimit = problem.head.control.constraints.inferAllDifferentNb, sLimit = problem.head.control.constraints.inferAllDifferentSize;
			List<VariableInteger[]> list = buildCliques(problem.variables, problem.features.collectedCtrsAtInit, nLimit, sLimit);
			for (VariableInteger[] scp : list)
				problem.allDifferent(scp);
			nBuiltCliques = list.size();
		}

		private boolean controlClique(Variable[] scp, List<Constraint> constraints) {
			for (int i = 0; i < scp.length; i++)
				for (int j = i + 1; j < scp.length; j++) {
					Variable x = scp[i], y = scp[j];
					Kit.control(constraints.stream().anyMatch(c -> c.scp.length == 2 && c.isIrreflexive() && c.involves(x, y)),
							() -> "not a clique with " + x + " " + y);
				}
			return true;
		}

		private void display(int cliqueId, VariableInteger[] scp) {
			System.out.println(" clique " + cliqueId + " of size " + scp.length + " {" + Kit.join(scp) + "}");
		}
	}

	/*************************************************************************
	 ***** Interfaces
	 *************************************************************************/

	public static final class DeducingAutomorphism {
		public static final String N_GENERATORS = "nGenerators";
		public static final String SYMMETRY_WALL_CLOCK_TIME = "symmetryWckTime";

		private Problem problem;

		private int nCurrentNodes;

		private int nCurrentColors;

		private int[] variableNodes; // 1D = variable id ; value = color id

		private Map<String, Variable> mapOfDomainColors;

		private List<Node> constraintNodes;

		private Map<String, int[]> mapOfRelationColors;

		private Map<Integer, List<Integer>> groupsOfColors; // 1D = color number ; value = list of node ids with this color

		public List<List<int[]>> generators;

		private Stopwatch stopwatch;

		private int nFusions;

		private String graphFileName;

		public DeducingAutomorphism(Problem pb) {
			this.problem = pb;
		}

		private class Node {
			private int id;

			private int color;

			private int[] neighbors;

			private Node(int id, int color) {
				this.id = id;
				this.color = color;
				neighbors = new int[0];
			}

			private Node(int id, int color, int[] neighbors) {
				this.id = id;
				this.color = color;
				this.neighbors = neighbors;
			}

			@Override
			public String toString() {
				String s = "node " + (id + 1) + " color=" + color + " neighbors=";
				for (int i = 0; i < neighbors.length; i++)
					s += (neighbors[i] + 1) + " ";
				return s;
			}
		}

		private void clear() {
			variableNodes = null;
			mapOfDomainColors.clear();
			constraintNodes.clear();
			mapOfRelationColors.clear();
			groupsOfColors.clear();
		}

		private void addColorNode(int id, int color) {
			groupsOfColors.computeIfAbsent(color, k -> new ArrayList<>()).add(id);
		}

		private Map<String, Domain> mapOfModifiedDomains;

		private String manageDomainKeyOf(Domain dom) {
			if (dom.nRemoved() == 0)
				return dom.typeName() + "0";
			if (mapOfModifiedDomains == null)
				mapOfModifiedDomains = new HashMap<>();
			for (int i = 1; true; i++) {
				String key = dom.typeName() + i;
				Domain d = mapOfModifiedDomains.get(key);
				if (d == null) {
					mapOfModifiedDomains.put(key, d);
					return key;
				} else if (dom.size() == d.size()) {
					boolean equal = true;
					for (int idx = dom.first(); equal && idx != -1; idx = dom.next(idx))
						if (!d.present(idx))
							equal = false;
					if (equal)
						return key;
				}
			}
		}

		private void buildVariableNodes(Variable[] vars) {
			mapOfDomainColors = new HashMap<>();
			variableNodes = new int[vars.length];

			for (int i = 0; i < vars.length; i++) {
				String key = manageDomainKeyOf(vars[i].dom);
				// System.out.println("domainKey = " + key + " for " + variables[i]);
				Variable var = mapOfDomainColors.get(key);
				if (var == null) {
					mapOfDomainColors.put(key, vars[i]);
					variableNodes[i] = nCurrentColors++;
				} else
					variableNodes[i] = variableNodes[var.num];
				addColorNode(i, variableNodes[i]);
			}
			nCurrentNodes = variableNodes.length;
		}

		private void buildConstraintNodes(Collection<Constraint> ctrs) {
			mapOfRelationColors = new HashMap<>();
			constraintNodes = new ArrayList<>();
			for (Constraint c : ctrs) {
				Variable[] scope = c.scp;
				String key = c.key; // TODO : pb with key null for pb HSp
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
				int v = nCurrentNodes;
				constraintNodes.add(new Node(nCurrentNodes, t[t.length - 1]));
				addColorNode(nCurrentNodes++, t[t.length - 1]);
				for (int i = 0; i < t.length - 1; i++) {
					constraintNodes.add(new Node(nCurrentNodes, t[i], new int[] { scope[i].num, v }));
					addColorNode(nCurrentNodes++, t[i]);
				}
			}
		}

		private void buildGAPEdges(PrintWriter out) {
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
					// cnt++;
					if (it.hasNext() || i < node.neighbors.length - 1)
						out.print(',');
				}
			}
			out.print(']');
		}

		private void buildGAPGroups(PrintWriter out) {
			out.print('[');
			Collection<List<Integer>> collection = groupsOfColors.values(); // iterator();
			Iterator<List<Integer>> it = collection.iterator();
			while (it.hasNext()) {
				List<Integer> list = it.next();
				out.print('[');
				for (int i = 0; i < list.size(); i++) {
					out.print(list.get(i) + 1);
					if (i < list.size() - 1)
						out.print(',');
				}
				out.print(']');
				if (it.hasNext())
					out.print(',');
			}
			out.print(']');
		}

		private void saveInGAPFormat() {
			try {
				PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(graphFileName = "graph" + new Random().nextInt() + ".gap")));
				// = "/tmp/graph" + random.nextInt() + ".gap";
				out.print("AutGroupGraph(UnderlyingGraph(EdgeOrbitsGraph( Group(()),");
				buildGAPEdges(out);
				out.print(',');
				out.print(nCurrentNodes);
				out.print(")),");
				buildGAPGroups(out);
				out.println(");");
				out.close();
			} catch (Exception e) {
				Kit.exit(e);
			}
		}

		private List<int[]> parseGenerator(String line) {
			List<int[]> list = new ArrayList<>();
			StringTokenizer st1 = new StringTokenizer(line, "()");
			while (st1.hasMoreTokens()) {
				String cycle = st1.nextToken();
				// System.out.println(cycle);
				StringTokenizer st2 = new StringTokenizer(cycle, ",");
				if (!st2.hasMoreTokens())
					break;
				int id = Integer.parseInt(st2.nextToken()) - 1;
				if (id >= variableNodes.length)
					break;
				int[] t = new int[st2.countTokens() + 1];
				t[0] = id;
				for (int i = 1; i < t.length; i++)
					t[i] = Integer.parseInt(st2.nextToken()) - 1;
				list.add(t);
			}
			return list;
		}

		private void runSaucy() {
			try {
				String command = System.getenv("HOME") + File.separator + "tools" + File.separator + "saucy-1.1" + File.separator + "saucy -t 20 -g "
						+ graphFileName;
				Kit.log.info("Command for symmetry breaking is " + command);
				Process p = Runtime.getRuntime().exec(command);

				BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream()));
				generators = new ArrayList<>();

				in.readLine();
				String line = in.readLine().trim();
				while (!line.equals("]")) {
					List<int[]> generator = parseGenerator(line);
					if (generator.size() > 0) // {
						generators.add(generator); // break; }
					// else
					// System.out.println(" not exploitable generator : " + line);
					line = in.readLine();
				}
				displayGenerators();
				in.close();
				p.waitFor();
				p.destroy();
				// Runtime.getRuntime().exec("rm " + graphFileName);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		private List<Constraint> buildConstraintsFor(Variable[] variables, Collection<Constraint> collectedConstraints) {
			List<Constraint> list = new ArrayList<>();
			for (List<int[]> generator : generators) {
				int[] cycle1 = generator.get(0);
				Variable x = variables[cycle1[0]];
				Variable y = variables[cycle1[1]];

				if (problem.head.control.problem.symmetryBreaking == ESymmetryBreaking.LE) { // we only consider the two first variables
					list.add(new Intension(problem, problem.api.vars(x, (Object) y), problem.api.le(x, y)));
				} else {
					List<Variable> list1 = new ArrayList<>(), list2 = new ArrayList<>();
					for (int[] cycle : generator)
						if (cycle.length == 2) {
							list1.add(variables[cycle[0]]);
							list2.add(variables[cycle[1]]);
						} else
							for (int i = 0; i < cycle.length; i++) {
								list1.add(variables[cycle[i]]);
								list2.add(variables[cycle[(i + 1) % cycle.length]]);
							}
					Variable[] t1 = list1.toArray(new Variable[list1.size()]), t2 = list2.toArray(new Variable[list2.size()]);
					Kit.control(Kit.isStrictlyIncreasing(t1));
					list.add(new LexicographicLE(problem, t1, t2));
				}
			}
			return list;
		}

		public List<Constraint> buildVariableSymmetriesFor(Variable[] vars, Collection<Constraint> cons) {
			stopwatch = new Stopwatch();
			groupsOfColors = new HashMap<>();
			buildVariableNodes(vars);
			buildConstraintNodes(cons);
			saveInGAPFormat();
			runSaucy();
			// displayGraph();
			clear();
			return buildConstraintsFor(vars, cons);
		}

		public void putInMap(Map<String, String> map) {
			map.put(N_GENERATORS, generators.size() + "");
			map.put("nbFusions", nFusions + "");
			map.put(SYMMETRY_WALL_CLOCK_TIME, stopwatch.wckTimeInSeconds() + "");
		}

		void displayGenerators() {
			if (problem.head.control.general.verbose > 0)
				for (List<int[]> generator : generators) {
					String s = "generator = ";
					for (int[] t : generator)
						s += "[ " + Kit.join(t) + " ]";
					System.out.println(s); // System.out.println();
				}
		}

		void displayGraph() {
			System.out.println("variableNodes");
			for (int i = 0; i < variableNodes.length; i++)
				System.out.println((i + 1) + ":" + variableNodes[i] + " ");
			System.out.println("constraintNodes");
			for (int i = 0; i < constraintNodes.size(); i++)
				System.out.println((i + 1) + ":" + constraintNodes.get(i) + " ");
		}
	}

}
