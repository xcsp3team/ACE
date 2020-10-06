package interfaces;

import utility.exceptions.MissingImplementationException;

public interface OptimizationCompatible {

	default long minComputableObjectiveValue() {
		throw new MissingImplementationException();
	}

	default long maxComputableObjectiveValue() {
		throw new MissingImplementationException();
	}

	long getLimit();

	void setLimit(long newLimit);

	long objectiveValue();
}
