/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package problem.cliques;

import java.util.Arrays;

import search.backtrack.SolverBacktrack;
import variables.Variable;

public class GraphManager {
	/**
	 * The tree solver at which the disconnector is attached.
	 */
	private SolverBacktrack solver;

	private int[] componentNumber; // index = variable id

	private Variable[] bestComponent;

	private int bestComponentSize;

	private int bestComponentNumber;

	private int nComponents;

	private int[] nodeOrdering;

	private boolean[] articulations;

	private int currentOrdering;

	public GraphManager(SolverBacktrack solver) {
		this.solver = solver;
		int nVariables = solver.pb.variables.length;
		componentNumber = new int[nVariables];
		nodeOrdering = new int[nVariables];
		articulations = new boolean[nVariables];
		bestComponent = new Variable[nVariables];
	}

	/**
	 * 
	 * @param x
	 *            the entry point
	 * @param currentComponentNumber
	 * @return a number denoting the size of the connex component if it represents a tree, a positive number denoting the size of the connex component
	 *         if it does not represents a tree
	 */
	private int determineConnexComponentOf(Variable x, int currentComponentNumber) {
		int cnt = 1;
		boolean tree = true;
		componentNumber[x.num] = currentComponentNumber;

		Variable[] neighbours = x.nghs;
		if (neighbours != null && neighbours.length <= solver.futVars.size()) {
			for (Variable neighbour : neighbours) {
				if (!neighbour.isFuture())
					continue;

				if (componentNumber[neighbour.num] == -1) {
					int result = determineConnexComponentOf(neighbour, currentComponentNumber);
					if (result > 0)
						tree = false;
					cnt += Math.abs(result);
				} else
					tree = false;
			}
		} else {
			for (Variable y : solver.futVars) {
				if (x == y || !x.isNeighbourOf(y))
					continue;
				if (componentNumber[y.num] == -1) {
					int result = determineConnexComponentOf(y, currentComponentNumber);
					if (result > 0)
						tree = false;
					cnt += Math.abs(result);
				} else
					tree = false;
			}
		}

		return (tree ? -cnt : cnt);
	}

	private boolean controlConnexComponents(Variable[] variables, int leftFrontier, int rightFrontier) {
		for (int i = 0; i < componentNumber.length; i++) {
			if (componentNumber[i] != -1) {
				boolean found = false;
				for (int j = leftFrontier; !found && j <= rightFrontier; j++)
					if (variables[j].num == i)
						found = true;
				if (!found)
					return false;
			}
		}
		return true;
	}

	public void determineConnexComponentsIn(Variable[] variables, int leftFrontier, int rightFrontier) {
		nComponents = 0;
		if (rightFrontier < leftFrontier)
			return;
		bestComponentNumber = -1;
		bestComponentSize = solver.pb.variables.length + 1;
		int bestTreeNumber = -1;
		int bestTreeSize = solver.pb.variables.length + 1;
		Arrays.fill(componentNumber, -1);

		for (int i = leftFrontier; i <= rightFrontier; i++) {
			if (!variables[i].isFuture() || componentNumber[variables[i].num] != -1)
				continue;
			int componentSize = determineConnexComponentOf(variables[i], nComponents);
			assert componentSize != 0;
			// System.out.println("componet size = " + componentSize);
			if (componentSize < 0 && Math.abs(componentSize) < bestTreeSize) {
				bestTreeSize = Math.abs(componentSize);
				bestTreeNumber = nComponents;
			}
			if (componentSize > 0 && componentSize < bestComponentSize) {
				bestComponentSize = componentSize;
				bestComponentNumber = nComponents;
			}
			nComponents++;
		}
		if (bestComponentNumber == -1) {
			bestComponentSize = bestTreeSize;
			bestComponentNumber = bestTreeNumber;
		}

		assert controlConnexComponents(variables, leftFrontier, rightFrontier);
		int cpt = 0;
		for (int i = leftFrontier; i <= rightFrontier; i++)
			if (componentNumber[variables[i].num] == bestComponentNumber)
				bestComponent[cpt++] = variables[i];
		assert nComponents == 0 || cpt == bestComponentSize : "cpt =" + cpt + " best = " + bestComponentSize + "nbC = " + nComponents;

		displayConnexComponents(variables, leftFrontier, rightFrontier);
		// System.out.println(" best = " + bestComponentSize + " nbC = " + nbComponents);

		// if (nbComponents > 1) {
		// // for (int i = 0; i < bestComponentSize; i++)
		// // System.out.print(bestComponent[i] + " ");
		// // System.out.println();
		// solver.getVariableOrderingHeuristic().setPriority(bestComponent[0]);
		// }

	}

	public void determineConnexComponents() {
		Variable[] variables = solver.futVars.toArray();
		determineConnexComponentsIn(variables, 0, variables.length - 1);
		//
		// bestComponentSize = solver.variables.length + 1;
		// Arrays.fill(componentNumber, -1);
		//
		// for (Variable fv = solver.getFirstFutureVariable(); fv != null; fv = solver.getNextFutureVariableAfter(fv))
		// {
		// if (componentNumber[fv.getId()] != -1)
		// continue;
		// int componentSize = determineConnexComponentOf(fv, nbComponents);
		// if (componentSize < bestComponentSize)
		// {
		// bestComponentSize = componentSize;
		// bestComponentNumber = nbComponents;
		// }
		// nbComponents++;
		// }
		// int cpt = 0;
		// for (Variable fv = solver.getFirstFutureVariable(); fv != null; fv = solver.getNextFutureVariableAfter(fv))
		// if (componentNumber[fv.getId()] == bestComponentNumber)
		// bestComponent[cpt++] = fv;
	}

	private void displayConnexComponents(Variable[] variables, int leftFrontier, int rightFrontier) {
		for (int i = 0; i < nComponents; i++) {
			int cpt = 0;
			System.out.print("Component " + i + " = { ");
			Variable var = null;
			for (int j = leftFrontier; j <= rightFrontier; j++) {
				if (componentNumber[variables[j].num] == i) {
					var = variables[j];
					cpt++;
					if (cpt < 10)
						System.out.print(variables[j] + " ");
				}
			}
			System.out.println((cpt >= 10 ? "..." : "") + "} with " + cpt + " elements" + (cpt == 1 ? " ddegrre = " + var.ddeg() : ""));
		}
	}

	private int searchAttachment(Variable varParent, Variable var, Variable varForbidden) {
		nodeOrdering[var.num] = ++currentOrdering;
		int min = currentOrdering;

		Variable[] neighbours = var.nghs;
		if (neighbours != null && neighbours.length <= solver.futVars.size()) {
			for (Variable neighbour : neighbours) {
				if (!neighbour.isFuture())
					continue;
				if (neighbour == varForbidden)
					continue;
				if (nodeOrdering[neighbour.num] == -1) {
					int attachment = searchAttachment(var, neighbour, varForbidden);
					min = Math.min(min, attachment);
					if (attachment >= nodeOrdering[var.num]) {
						articulations[var.num] = true;
						articulationPoint = var;
					}
				} else if (nodeOrdering[neighbour.num] < nodeOrdering[var.num] && neighbour != varParent) {
					min = Math.min(min, nodeOrdering[neighbour.num]);
					nbCycles++;
				}
			}
		} else {
			for (Variable y : solver.futVars) {
				if (var != y && var.isNeighbourOf(y) && y != varForbidden) {
					if (nodeOrdering[y.num] == -1) {
						int attachment = searchAttachment(var, y, varForbidden);
						min = Math.min(min, attachment);
						if (attachment >= nodeOrdering[var.num]) {
							articulations[var.num] = true;
							articulationPoint = var;
						}
					} else if (nodeOrdering[y.num] < nodeOrdering[var.num] && y != varParent) {
						min = Math.min(min, nodeOrdering[y.num]);
						nbCycles++;
					}
				}
			}
		}

		// Variable[] neighbours = variable.getNeighbours();
		// for (int i = 0; i < neighbours.length; i++) {
		// if (!neighbours[i].isFuture() || neighbours[i] == forbiddenVariable)
		// continue;
		// if (nodeOrdering[neighbours[i].getId()] == -1) {
		// int attachment = searchAttachment(variable, neighbours[i], forbiddenVariable);
		// min = Math.min(min, attachment);
		// if (attachment >= nodeOrdering[variable.getId()]) {
		// articulations[variable.getId()] = true;
		// articulationPoint = variable;
		// }
		// } else if (nodeOrdering[neighbours[i].getId()] < nodeOrdering[variable.getId()] && neighbours[i] != parent) {
		// min = Math.min(min, nodeOrdering[neighbours[i].getId()]);
		// nbCycles++;
		// }
		// }

		return min;
	}

	private int nbCycles;

	private Variable articulationPoint;

	private Variable searchArticulationsFrom(Variable x, Variable varForbidden, boolean allowedTreeArticulation) {
		assert x != varForbidden;
		nodeOrdering[x.num] = ++currentOrdering;
		nbCycles = 0;
		articulationPoint = null;
		int nbConnexComponentsIfAssigned = 0;

		Variable[] neighbours = x.nghs;
		if (neighbours != null && neighbours.length <= solver.futVars.size()) {
			for (Variable neighbour : neighbours) {
				if (!neighbour.isFuture())
					continue;
				if (neighbour == varForbidden || nodeOrdering[neighbour.num] != -1)
					continue;
				searchAttachment(x, neighbour, varForbidden);
				nbConnexComponentsIfAssigned++;
			}
		} else {
			for (Variable y = solver.futVars.first(); y != null; y = solver.futVars.next(x)) {
				if (x != y && x.isNeighbourOf(y) && y != varForbidden && nodeOrdering[y.num] == -1) {
					searchAttachment(x, y, varForbidden);
					nbConnexComponentsIfAssigned++;
				}
			}
		}

		// Variable[] neighbours = variable.getNeighbours();
		// for (int i = 0; i < neighbours.length; i++) {
		// if (!neighbours[i].isFuture() || neighbours[i] == forbiddenVariable || nodeOrdering[neighbours[i].getId()] !=
		// -1)
		// continue;
		// searchAttachment(variable, neighbours[i], forbiddenVariable);
		// nbConnexComponentsIfAssigned++;
		// }

		if (nbConnexComponentsIfAssigned > 1) {
			articulations[x.num] = true;
			articulationPoint = x;
		}
		return (!allowedTreeArticulation && nbCycles == 0 ? null : articulationPoint);
	}

	public void displayArticulations() {
		boolean found = false;
		for (int i = 0; i < articulations.length; i++)
			if (articulations[i]) {
				System.out.print((!found ? "Articulation " : "") + i + " ");
				found = true;
			}
		if (found)
			System.out.println();

	}

	// public Variable searchAllArticulations()
	// {
	// currentOrdering = -1;
	// Arrays.fill(nodeOrdering, -1);
	// Arrays.fill(articulations, false);
	// for (Variable futureVariable = solver.getFirstFutureVariable();
	// futureVariable != null;
	// futureVariable = solver.getNextFutureVariableAfter(futureVariable))
	// {
	// if (nodeOrdering[futureVariable.id] != -1)
	// continue;
	// searchArticulationsFrom(futureVariable);
	// }
	// displayArticulations();
	// for (int i = 0; i < articulations.length; i++)
	// if (articulations[i])
	// return solver.getVariable(i);
	// return null;
	// }

	public Variable findFirstArticulation(Variable varForbidden, boolean allowedTreeArticulation) {
		currentOrdering = -1;
		Arrays.fill(nodeOrdering, -1);
		Arrays.fill(articulations, false);
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			if (x == varForbidden || nodeOrdering[x.num] != -1)
				continue;
			Variable articulation = searchArticulationsFrom(x, varForbidden, allowedTreeArticulation);
			if (articulation != null) {
				System.out.println("Articulation " + articulation + " allowed = " + allowedTreeArticulation);
				return articulation;
			}
		}
		return null;
	}

	public Variable findFirstArticulation(boolean allowedTreeArticulation) {
		return findFirstArticulation(null, allowedTreeArticulation);
	}

	public Variable findFirstVariableInArticulationPair() {
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			Variable varArticulation = findFirstArticulation(x, true);
			if (varArticulation != null)
				return varArticulation;
		}
		return null;
	}
}
// public Variable findFirst

// private void analyseGraphFrom(Variable variable, int currentComponentNumber)
// {
//
// Constraint[] constraints = variable.constraints;
// for (int i = 0; i < constraints.length; i++)
// {
// for (Variable fv = constraints[i].getFirstFutureVariable(); fv != null; fv =
// constraints[i].getNextFutureVariableAfter(fv))
// if (componentNumber[fv.getId()] == -1)
// size += determineConnexComponentOf(fv, currentComponentNumber);
// }
// return size;
//
// int size = 1;
// componentNumber[variable.getId()] = currentComponentNumber;
//
// nodeOrdering[variable.getId()] = ++currentOrdering;
// int nbConnexComponentsIfAssigned = 0;
//
// Constraint[] constraints = variable.constraints;
// for (int i = 0; i < constraints.length; i++)
// {
// for (Variable fv = constraints[i].getFirstFutureVariable(); fv != null; fv =
// constraints[i].getNextFutureVariableAfter(fv))
// {
// if (nodeOrdering[fv.getId()] == -1)
// {
// searchAttachment(variable, fv);
// nbConnexComponentsIfAssigned++;
// }
// }
// }
// articulations[variable.getId()] = nbConnexComponentsIfAssigned > 1;
// }
//
// public Variable analyseGraph()
// {
// currentOrdering = -1;
// Arrays.fill(nodeOrdering, -1);
// Arrays.fill(articulations, false);
//
// nbComponents = 0;
// bestComponentSize = solver.variables.length + 1;
// Arrays.fill(componentNumber, -1);
//
// for (Variable futureVariable = solver.getFirstFutureVariable();
// futureVariable != null;
// futureVariable = solver.getNextFutureVariableAfter(futureVariable))
// {
//
// if (nodeOrdering[futureVariable.id] != -1)
// continue;
// analyseGraphFrom(futureVariable, nbComponents);
//
// int componentSize = determineConnexComponentOf(futureVariable, nbComponents);
// if (componentSize < bestComponentSize)
// {
// bestComponentSize = componentSize;
// bestComponentNumber = nbComponents;
// }
// nbComponents++;
//
// }
// displayArticulations();
// for (int i = 0; i < articulations.length; i++)
// if (articulations[i])
// return solver.getVariable(i);
// return null;
// }
