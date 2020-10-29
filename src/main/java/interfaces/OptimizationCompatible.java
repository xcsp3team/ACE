package interfaces;

public interface OptimizationCompatible {

	long getLimit();

	void setLimit(long newLimit);

	long minComputableObjectiveValue();

	long maxComputableObjectiveValue();

	long objectiveValue();
}
