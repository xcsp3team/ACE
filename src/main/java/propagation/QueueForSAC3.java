/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.WdegOnDom;
import search.backtrack.SolverBacktrack;
import utility.Reflector;
import variables.Variable;

public final class QueueForSAC3 {

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

	public final class Fifo implements CellSelector {
		@Override
		public Cell select() {
			if (priorityToSingletons) {
				Cell cell = firstSingletonCell();
				if (cell != null)
					return cell;
			}
			for (Cell cell = head; cell != null; cell = cell.next) // first valid cell
				if (cell.x.dom.isPresent(cell.a))
					return cell;
			return null;
		}
	}

	public final class Lifo implements CellSelector {
		@Override
		public Cell select() {
			if (priorityToSingletons) {
				Cell cell = firstSingletonCell();
				if (cell != null)
					return cell;
			}
			for (Cell cell = tail; cell != null; cell = cell.prev) // last valid cell
				if (cell.x.dom.isPresent(cell.a))
					return cell;
			return null;
		}
	}

	public final class CellIterator implements CellSelector {
		protected HeuristicVariables heuristic;

		public CellIterator() {
			this.heuristic = new WdegOnDom(solver, false); // hard coding ; alternatives: null, new Dom(solver, false), new DdegOnDom(solver, false) ...
		}

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
					double evaluation = heuristic == null ? sizes[x.num] : heuristic.scoreOptimizedOf(x);
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

	private SolverBacktrack solver;

	private boolean priorityToSingletons;

	private Cell head, tail, trash;
	private Cell priorityCell;

	public int size;

	private Cell[][] positions;

	private int[] sizes;

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
		if (sizes[x.num] == 0)
			return;
		for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
			Cell cell = positions[x.num][a];
			if (cell != null) {
				priorityCell = cell;
				break;
			}
		}
	}

	private Cell firstSingletonCell() {
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			if (x.dom.size() == 1) {
				Cell cell = positions[x.num][x.dom.first()];
				if (cell != null)
					return cell;
			}
		}
		return null;
	}

	public Cell pickNextCell() {
		if (size == 0)
			return null;
		Cell cell = priorityCell != null ? priorityCell : cellSelector.select();
		priorityCell = null;
		if (cell != null)
			remove(cell);
		return cell; // even if removed, fields x and a are still operational (if cell is not null)
	}

	public QueueForSAC3(SolverBacktrack solver, boolean priorityToSingletons) {
		this.solver = solver;
		this.priorityToSingletons = priorityToSingletons;
		this.positions = Stream.of(solver.pb.variables).map(x -> new Cell[x.dom.initSize()]).toArray(Cell[][]::new);
		IntStream.range(0, Variable.nInitValuesFor(solver.pb.variables)).forEach(i -> trash = new Cell(trash));
		this.sizes = new int[solver.pb.variables.length];
		String s = solver.rs.cp.settingPropagation.classForSACSelector.substring(solver.rs.cp.settingPropagation.classForSACSelector.lastIndexOf('$') + 1);
		this.cellSelector = Reflector.buildObject(s, CellSelector.class, this);
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
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			if (onlyBounds) {
				add(x, x.dom.first());
				add(x, x.dom.last());
			} else
				for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
					add(x, a);
		}
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