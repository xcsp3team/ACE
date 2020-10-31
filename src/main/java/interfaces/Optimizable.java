package interfaces;

public interface Optimizable {

	long getLimit();

	void setLimit(long newLimit);

	long minComputableObjectiveValue();

	long maxComputableObjectiveValue();

	long objectiveValue();
}
