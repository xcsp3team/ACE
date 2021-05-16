/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.intension;

import java.util.stream.Stream;

import constraints.Constraint;
import interfaces.FilteringSpecific;
import interfaces.Tags.TagAC;
import problem.Problem;
import variables.Domain;
import variables.Variable;

public abstract class Primitive extends Constraint implements FilteringSpecific {

	protected final void defineKey(Object... datas) {
		StringBuilder sb = signature().append(' ').append(getClass().getSimpleName());
		Stream.of(datas).forEach(data -> sb.append(' ').append(data.toString()));
		this.key = sb.toString();
	}

	public Primitive(Problem pb, Variable[] scp) {
		super(pb, scp);
		defineKey(); // most of the time, no specific data (otherwise, call it again in subclasses with the right args)
	}

	public static final class Disjonctive2D extends Primitive implements TagAC {

		final Variable x1, x2, y1, y2;
		final int w1, w2, h1, h2;
		final Domain dx1, dx2, dy1, dy2;

		@Override
		public boolean checkValues(int[] tuple) {
			return tuple[0] + w1 <= tuple[1] || tuple[1] + w2 <= tuple[0] || tuple[2] + h1 <= tuple[3] || tuple[3] + h2 <= tuple[2];
		}

		public Disjonctive2D(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2, int w1, int w2, int h1, int h2) {
			super(pb, new Variable[] { x1, x2, y1, y2 });
			control(scp.length == 4);
			this.x1 = x1;
			this.x2 = x2;
			this.y1 = y1;
			this.y2 = y2;
			this.w1 = w1;
			this.w2 = w2;
			this.h1 = h1;
			this.h2 = h2;
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dy1 = y1.dom;
			this.dy2 = y2.dom;
			defineKey(w1, w2, h1, h2);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			boolean bx1 = dx1.firstValue() + w1 <= dx2.lastValue();
			boolean bx2 = dx2.firstValue() + w2 <= dx1.lastValue();
			boolean bx = bx1 || bx2;
			boolean by1 = dy1.firstValue() + h1 <= dy2.lastValue();
			boolean by2 = dy2.firstValue() + h2 <= dy1.lastValue();
			boolean by = by1 || by2;
			if (bx && by)
				return true;
			if (!bx && !by)
				return false;
			if (bx)
				return dx1.removeValuesInRange(dx2.lastValue() - w1 + 1, dx2.firstValue() + w2)
						&& dx2.removeValuesInRange(dx1.lastValue() - w2 + 1, dx1.firstValue() + w1);
			return dy1.removeValuesInRange(dy2.lastValue() - h1 + 1, dy2.firstValue() + h2)
					&& dy2.removeValuesInRange(dy1.lastValue() - h2 + 1, dy1.firstValue() + h1);

		}
	}
}
