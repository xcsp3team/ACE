package utility;

public class Enums {

	public static enum Branching {
		BIN, RES, NON;
	}

	public static enum OptimizationStrategy {
		INCREASING, DECREASING, DICHOTOMIC;
	}

	public static enum Extension {
		V, VA, STR1, STR2, STR3, STR1NEG, STR2NEG, CT, CMDD, CMDDSHORT, GAC4, RPWC, RPWC2;
	}

	public enum Extraction {
		DEC_VAR, DEC_CON, VAR, CON, INC, INC_FIRST, MAX_CSP;
	}

	public static enum LearningNogood {
		NO, RST, MIN_STD, RST_MIN, RST_SYM;

		public boolean isRstType() {
			return this == RST || this == RST_MIN || this == RST_SYM;
		}
	}

	public enum LearningIps {
		NO, EQUIVALENCE, DOMINANCE;
	}

	public static enum TypeOutput {
		RESOLUTIONS,
		RESOLUTION,
		INSTANCE,
		DOMAINS,
		VARIABLES,
		CONSTRAINTS,
		CONSTRAINT_TYPES,
		OBJECTIVES,
		OBJECTIVE,
		SOLVER,
		PREPROCESSING,
		RUN,
		SEARCH,
		GLOBAL,
		ERROR,
		EXPIRED,
		CRASHED,
		SAT,
		UNSAT,
		UNKNOWN,
		ALL,
		KERNEL;

		@Override
		public String toString() {
			return name().toLowerCase();
		}
	}

	public static enum RestartMeasure {
		FAILED, WRONG, BACKTRACK, SOLUTION;
	}

	public static enum ExportMode {
		NO,
		INTENSION,
		EXTENSION, // EXTENSION is for automatic mode (either supports or conflicts)
		EXTENSION_SUPPORTS,
		EXTENSION_CONFLICTS;
	}

	public enum SingletonStrategy {
		ANY, FIRST, LAST;
	}

	public static enum Stopping {
		FULL_EXPLORATION, REACHED_GOAL, EXCEEDED_TIME;
	}

	public static enum SymmetryBreaking {
		NO, LE, LEX;
	}

	public static enum ConstraintWeighting {
		VAR, UNIT, CACD, CHS; // UNIT is for classical wdeg, cacd its variant (ICTAI'19) and CHS (from Marseille guys)
	}

}
