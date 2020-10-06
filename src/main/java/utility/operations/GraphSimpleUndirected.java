package utility.operations;

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import utility.Kit;

public class GraphSimpleUndirected {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/
	// int[][] m = { { 1, 5, 6, 2 }, { 3, 9, 10, 1 }, { 7, 9, 3, 5 }, { 5, 8, 6, 2 } };
	// Kit.prn(Graph.determinant(m));
	// int[][] m1 = { { 1, 0, 1 }, { 0, 1, 0 } };
	// int[][] m2 = { { 1, 0 }, { 0, 1 }, { 1, 1 } };
	// Kit.prn(Kit.implode2D(Graph.product(m1, m2)));

	public static GraphSimpleUndirected loadGraph(String fileName) {
		try (BufferedReader in = new BufferedReader(new FileReader(fileName))) {
			int nbNodes = Integer.parseInt(in.readLine());
			List<int[]> edges = new ArrayList<>();
			for (int i = 0; i < nbNodes; i++) {
				StringTokenizer st = new StringTokenizer(in.readLine());
				int nbNeighbours = Integer.parseInt(st.nextToken());
				for (int cnt = 0; cnt < nbNeighbours; cnt++)
					edges.add(new int[] { i, Integer.parseInt(st.nextToken()) });
			}
			GraphSimpleUndirected g = new GraphSimpleUndirected(nbNodes, edges);
			// Kit.prn(g);
			return g;
		} catch (Exception e) {
			return (GraphSimpleUndirected) Kit.exit(e);
		}
	}

	public static int determinant(int[][] matrix) {
		if (matrix.length == 1) // bottom case of recursion. size 1 matrix determinant is itself.
			return matrix[0][0];
		int determinantValue = 0;
		for (int i = 0; i < matrix.length; i++) { // finds determinant using row-by-row expansion
			int[][] smaller = new int[matrix.length - 1][matrix.length - 1]; // creates smaller matrix- values not in same row, column
			for (int a = 1; a < matrix.length; a++)
				for (int b = 0; b < matrix.length; b++)
					if (b < i)
						smaller[a - 1][b] = matrix[a][b];
					else if (b > i)
						smaller[a - 1][b - 1] = matrix[a][b];
			determinantValue += (i % 2 == 0 ? 1 : -1) * matrix[0][i] * determinant(smaller);
		}
		return determinantValue;
	}

	public static long[][] product(long[][] m1, long[][] m2) {
		int n = m2.length;
		Kit.control(m1[0].length == n);
		long[][] m = new long[m1.length][m2[0].length];
		for (int i = 0; i < m.length; i++)
			for (int j = 0; j < m[i].length; j++) {
				int sum = 0;
				for (int k = 0; k < n; k++)
					sum += m1[i][k] * m2[k][j];
				m[i][j] = sum;
			}
		return m;
	}

	public static int[][] transposee(int[][] m) {
		int[][] p = new int[m[0].length][m.length];
		for (int i = 0; i < p.length; i++)
			for (int j = 0; j < p[i].length; j++)
				p[i][j] = m[j][i];
		return p;
	}

	public static int[][] quadratique1(int[][] m) {
		int[][] p = new int[m.length][m.length];
		for (int i = 0; i < p.length; i++)
			for (int j = 0; j < p[i].length; j++) {
				int sum = 0;
				for (int k = 0; k < m[0].length; k++)
					sum += m[i][k] * m[j][k];
				m[i][j] = sum;
			}
		return p;
	}

	public static int[][] quadratique2(int[][] m) {
		int[][] p = new int[m[0].length][m[0].length];
		for (int i = 0; i < m.length; i++)
			for (int j = 0; j < m[i].length; j++) {
				int sum = 0;
				for (int k = 0; k < m[0].length; k++)
					sum += m[k][i] * m[k][j];
				m[i][j] = sum;
			}
		return p;
	}

	/**********************************************************************************************
	 * Class
	 *********************************************************************************************/

	public final int nNodes, nEdges;

	public final long[][] adjacency;

	public int[][] nodesAtDistance1;

	public int[][] nodesAtDistance2;

	public int[][] nodesAtDistance1And2;

	private int[] cacheDegrees;

	public int[] degrees() {
		if (cacheDegrees == null)
			cacheDegrees = IntStream.range(0, nNodes).map(i -> (int) IntStream.range(0, nNodes).filter(j -> adjacency[i][j] == 1).count()).toArray();
		return cacheDegrees;
	}

	public int[] getNodesWithDegreeLT(int v) {
		return IntStream.range(0, nNodes).filter(i -> degrees()[i] < v).toArray();
	}

	public GraphSimpleUndirected(int nNodes, long[][] adjacency) {
		this.nNodes = nNodes;
		this.adjacency = adjacency;
		this.nEdges = -1; // TODO
	}

	public GraphSimpleUndirected(int nNodes, List<int[]> edges) {
		this.nNodes = nNodes;
		this.nEdges = edges.size();
		this.adjacency = new long[nNodes][nNodes];
		for (int[] t : edges) {
			adjacency[t[0]][t[1]] = 1;
			adjacency[t[1]][t[0]] = 1;
		}
	}

	public GraphSimpleUndirected(GraphSimpleUndirected g1, GraphSimpleUndirected g2) {
		Kit.control(g1.nNodes == g2.nNodes);
		this.nNodes = g1.nNodes;
		this.adjacency = new long[nNodes][nNodes];
		long[][] m1 = g1.adjacency, m2 = g2.adjacency;
		for (int i = 0; i < nNodes; i++)
			for (int j = 0; j <= i; j++) {
				int sum = 0;
				for (int k : g1.nodesAtDistance1[i])
					// = 0; k < nbNodes; k++)
					sum += m1[i][k] * m2[k][j];
				adjacency[i][j] = adjacency[j][i] = sum;
			}
		this.nEdges = -1; // TODO
	}

	public int[][] computeNodesAtDistance1() {
		nodesAtDistance1 = new int[nNodes][];
		for (int i = 0; i < nNodes; i++) {
			List<Integer> list = new ArrayList<>();
			for (int j = 0; j < nNodes; j++)
				if (i != j && adjacency[i][j] != 0)
					list.add(j);
			nodesAtDistance1[i] = Kit.intArray(list);
		}
		return nodesAtDistance1;
	}

	public int[][] computeNodesAtDistance2() {
		nodesAtDistance2 = new int[nNodes][];
		for (int i = 0; i < nNodes; i++) {
			List<Integer> list = new ArrayList<>();
			for (int j = 0; j < nNodes; j++)
				if (i != j)
					for (int k = 0; k < nNodes; k++)
						if (k != i && k != j && adjacency[i][k] != 0 && adjacency[j][k] != 0) {
							list.add(j);
							break;
						}
			nodesAtDistance2[i] = Kit.intArray(list);
		}
		return nodesAtDistance2;
	}

	public int[][] computeNodesAtDistance1And2() {
		nodesAtDistance1And2 = new int[nNodes][];
		for (int i = 0; i < nNodes; i++) {
			List<Integer> list = new ArrayList<>();
			for (int j = 0; j < nNodes; j++)
				if (i != j && adjacency[i][j] != 0)
					for (int k = 0; k < nNodes; k++)
						if (k != i && k != j && adjacency[i][k] != 0 && adjacency[j][k] != 0) {
							list.add(j);
							break;
						}
			nodesAtDistance1And2[i] = Kit.intArray(list);
		}
		return nodesAtDistance1And2;
	}

	public GraphSimpleUndirected copy() {
		return new GraphSimpleUndirected(nNodes, Stream.of(adjacency).map(t -> t.clone()).toArray(long[][]::new));
	}

	public int[][] edges(boolean includingSymmetrical) {
		return IntStream.range(0, nNodes).mapToObj(
				i -> IntStream.range(includingSymmetrical ? 0 : i + 1, nNodes).filter(j -> i != j && adjacency[i][j] == 1).mapToObj(j -> new int[] { i, j }))
				.flatMap(s -> s).toArray(int[][]::new);
	}

	public int[] selfLoops() {
		return IntStream.range(0, nNodes).filter(i -> adjacency[i][i] == 1).toArray();
	}

	public int[] neighborsOf(int i) {
		return IntStream.range(0, nNodes).filter(j -> adjacency[i][j] == 1).toArray();
	}

	@Override
	public String toString() {
		return nNodes + " \n" + Kit.join(adjacency) + "\n"
				+ IntStream.range(0, nNodes).mapToObj(i -> "Node " + i + " : " + Utilities.join(neighborsOf(i))).collect(Collectors.joining("\n"));
	}

	/**********************************************************************************************
	 * Experimental
	 *********************************************************************************************/

	private int[] visited;
	private int[] stack;
	private int top = -1;
	private int[] tmp;
	private List<int[]> cycles;

	void visit(int node, int parent) {
		visited[node] = 1;
		stack[++top] = node;
		// Kit.prn("stack " + node + " top = " + top);
		for (int i = 0; i < adjacency[node].length; i++) {
			if (adjacency[node][i] == 1) {
				if (visited[i] == 2 || i == parent)
					continue;
				else if (visited[i] == 1) {
					int nbCycleNodes = 0;
					tmp[nbCycleNodes++] = stack[top];
					for (int j = top - 1; j >= 0; j--) {
						tmp[nbCycleNodes++] = stack[j];
						if (stack[j] == i) {
							break;
						}
					}
					int[] cycle = new int[nbCycleNodes];
					System.arraycopy(tmp, 0, cycle, 0, nbCycleNodes);
					cycles.add(cycle);
				} else
					visit(i, node);
			}
		}
		visited[node] = 2;
		top--;
		// Kit.prn(" top after = " + top);
	}

	public void cycles() {
		tmp = new int[nNodes];
		stack = new int[nNodes];
		visited = new int[nNodes];
		cycles = new ArrayList<>();
		for (int i = 0; i < nNodes; i++)
			if (visited[i] == 0)
				visit(i, -1);
		Kit.log.finest(() -> Kit.join(Kit.intArray2D(cycles)));
	}

}

// public long[] copyAdjacenceAtRow(long[] t, boolean removeDiagonal, int i) {
// Kit.control(t.length == (removeDiagonal ? nNodes - 1 : nNodes));
// if (removeDiagonal) {
// for (int cnt = 0, j = 0; j < nNodes; j++)
// if (i != j)
// t[cnt++] = adjacency[i][j];
// } else
// System.arraycopy(adjacency[i], 0, t, 0, nNodes);
// return t;
// }
//
// public long[][] copyAdjacence(long[][] m, boolean removeDiagonal) {
// Kit.control(m.length == nNodes);
// for (int i = 0; i < m.length; i++)
// copyAdjacenceAtRow(m[i], removeDiagonal, i);
// return m;
// }
