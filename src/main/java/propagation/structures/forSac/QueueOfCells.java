/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.structures.forSac;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import heuristics.variables.HeuristicVariables;
import heuristics.variables.HeuristicVariablesDynamic.DDegOnDom;
import heuristics.variables.HeuristicVariablesDynamic.Dom;
import heuristics.variables.dynamic.WDegOnDom;
import search.backtrack.SolverBacktrack;
import utility.Reflector;
import variables.Variable;

public final class QueueOfCells {

	public final class Cell {
		public Variable x;
		public int a;

		private Cell prev, next;

		private Cell(Cell next) {
			this.next = next;
		}

		private void set(Variable x, int a, Cell prev, Cell next) {
			this.x = x;
			this.a = a;
			this.prev = prev;
			this.next = next;
		}
	}

	public interface CellSelector {
		Cell select();
	}

	public final class FifoSelector implements CellSelector {
		@Override
		public Cell select() {
			if (priorityToSingletons) {
				Cell cell = getFirstSingletonCell();
				if (cell != null)
					return cell;
			}
			return getFirstValidCell();
		}
	}

	public final class LifoSelector implements CellSelector {
		@Override
		public Cell select() {
			if (priorityToSingletons) {
				Cell cell = getFirstSingletonCell();
				if (cell != null)
					return cell;
			}
			return getLastValidCell();
		}
	}

	private abstract class VariableIteratingSelector implements CellSelector {
		protected abstract double evaluate(Variable x);

		@Override
		public Cell select() {
			Cell bestCell = null;
			double bestEvaluation = -1;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (sizes[x.num] == 0)
					continue;
				if (priorityToSingletons && x.dom.size() == 1) {
					Cell cell = positions[x.num][x.dom.first()];
					if (cell != null)
						return cell;
				} else {
					double evaluation = evaluate(x);
					if (bestCell == null || evaluation > bestEvaluation) {
						for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
							Cell cell = positions[x.num][a];
							if (cell != null) {
								bestCell = cell;
								bestEvaluation = evaluation;
								break;
							}
						}
					}
				}
			}
			return bestCell;
		}
	}

	public final class SizeSelector extends VariableIteratingSelector {
		@Override
		protected double evaluate(Variable x) {
			return sizes[x.num];
		}
	}

	private abstract class HeuristicSelector extends VariableIteratingSelector {
		protected HeuristicVariables varHeuristic;

		@Override
		protected double evaluate(Variable x) {
			return varHeuristic.scoreOptimizedOf(x);
		}
	}

	public final class DomSelector extends HeuristicSelector {
		public DomSelector() {
			varHeuristic = new Dom(solver, false);
		}
	}

	public final class DDegOnDomSelector extends HeuristicSelector {
		public DDegOnDomSelector() {
			varHeuristic = new DDegOnDom(solver, false);
		}
	}

	public final class WDegOnDomSelector extends HeuristicSelector {
		public WDegOnDomSelector() {
			varHeuristic = new WDegOnDom(solver, false);
		}
	}

	private SolverBacktrack solver;

	private boolean priorityToSingletons;

	private Cell head, tail, trash;
	private Cell priorityCell;

	public int size;

	private Cell[][] positions; // 1D = variable id; 2D = index;

	private int[] sizes; // 1D = variable id

	private CellSelector cellSelector;

	public boolean isPresent(Variable x, int a) {
		return positions[x.num][a] != null;
	}

	public void setPriorityTo(Variable x, int a) {
		assert priorityCell == null && isPresent(x, a);
		priorityCell = positions[x.num][a];
	}

	public void setPriorityOf(Variable x) {
		assert priorityCell == null;
		if (sizes[x.num] != 0) {
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
				Cell cell = positions[x.num][a];
				if (cell != null) {
					priorityCell = cell;
					break;
				}
			}
		}
	}

	public Cell getFirstValidCell() {
		for (Cell cell = head; cell != null; cell = cell.next)
			if (cell.x.dom.isPresent(cell.a))
				return cell;
		return null;
	}

	public Cell getLastValidCell() {
		for (Cell cell = tail; cell != null; cell = cell.prev)
			if (cell.x.dom.isPresent(cell.a))
				return cell;
		return null;
	}

	private Cell getFirstSingletonCell() {
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			if (x.dom.size() == 1) {
				Cell cell = positions[x.num][x.dom.first()];
				if (cell != null)
					return cell;
			}
		}
		return null;
	}

	public Cell getNextCell() {
		if (size == 0)
			return null;
		if (priorityCell != null) {
			Cell cell = priorityCell;
			priorityCell = null;
			return cell;
		}
		return cellSelector.select();
	}

	public Cell pickNextCell() {
		Cell cell = getNextCell();
		if (cell != null)
			remove(cell);
		return cell;
	}

	public QueueOfCells(SolverBacktrack solver, boolean priorityToSingletons) {
		this.solver = solver;
		this.priorityToSingletons = priorityToSingletons;
		positions = Stream.of(solver.pb.variables).map(x -> new Cell[x.dom.initSize()]).toArray(Cell[][]::new);
		IntStream.range(0, Variable.nInitValuesFor(solver.pb.variables)).forEach(i -> trash = new Cell(trash));
		sizes = new int[solver.pb.variables.length];
		String s = solver.rs.cp.propagating.classForSACSelector.substring(solver.rs.cp.propagating.classForSACSelector.lastIndexOf('$') + 1);
		cellSelector = Reflector.buildObject(s, CellSelector.class, this);
		// this is needed when calling an intern class constructor by reflection
	}

	public void clear() {
		size = 0;
		for (int i = 0; i < positions.length; i++)
			for (int j = 0; j < positions[i].length; j++)
				positions[i][j] = null;
		Arrays.fill(sizes, 0);
		if (head == null)
			return;
		if (trash != null) {
			tail.next = trash;
			trash.prev = tail;
		}
		trash = head;
		head = tail = null;
	}

	public void add(Variable x, int a) {
		if (positions[x.num][a] != null)
			return;
		Cell cell = trash;
		trash = trash.next;
		cell.set(x, a, tail, null);
		if (head == null)
			head = cell;
		else
			tail.next = cell;
		tail = cell;
		positions[x.num][a] = cell;
		sizes[x.num]++;
		size++;
	}

	public void remove(Cell cell) {
		Variable x = cell.x;
		int a = cell.a;
		Cell prev = cell.prev;
		Cell next = cell.next;
		if (prev == null)
			head = next;
		else
			prev.next = next;
		if (next == null)
			tail = prev;
		else
			next.prev = prev;
		cell.next = trash;
		trash = cell;
		positions[x.num][a] = null;
		sizes[x.num]--;
		size--;
	}

	public boolean remove(Variable x, int a) {
		Cell cell = positions[x.num][a];
		if (cell == null)
			return false;
		remove(cell);
		return true;
	}

	public void fill(boolean onlyBounds) {
		clear();
		solver.futVars.execute(x -> {
			if (onlyBounds) {
				add(x, x.dom.first());
				add(x, x.dom.last());
			} else
				for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
					add(x, a);
		});
	}

	public void fill() {
		fill(false);
	}

	public void display() {
		for (Cell cell = head; cell != null; cell = cell.next)
			System.out.print(cell.x + "-" + cell.a + " ");
		System.out.println();
	}
}