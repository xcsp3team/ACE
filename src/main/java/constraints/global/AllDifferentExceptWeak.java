package constraints.global;

import java.util.Map;

import org.xcsp.common.Utilities;

import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACUnguaranteed;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public class AllDifferentExceptWeak extends AllDifferentAbstract implements TagGACUnguaranteed, TagFilteringPartialAtEachCall {

	@Override
	public boolean checkValues(int[] t) {
		return Kit.allDifferentValues(t, exceptValues);
	}

	private int[] exceptValues;

	public AllDifferentExceptWeak(Problem pb, Variable[] scp, int[] exceptValues) {
		super(pb, scp);
		this.exceptValues = exceptValues;
		defineKey(Kit.join(exceptValues));
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1) {
			int v = x.dom.uniqueValue();
			if (Utilities.indexOf(v, exceptValues) != -1)
				return true;
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y != x && y.dom.removeValueIfPresent(v) == false)
					return false;
			}
		}
		return true;
	}

	@Override
	public Map<String, Object> mapXCSP() {
		Map<String, Object> map = super.mapXCSP();
		map.put(EXCEPT, Kit.join(exceptValues));
		return map;
	}
}
