package interfaces;

import variables.Variable;

@FunctionalInterface
public interface FilteringSpecific {
	boolean runPropagator(Variable evt);
}
