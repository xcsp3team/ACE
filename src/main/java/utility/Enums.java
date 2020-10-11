/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility;

public class Enums {

	public static enum EBranching {
		BIN, RES, NON;
	}

	public static enum EBinaryEncoding {
		NO, DUAL, HIDDEN, DOUBLE;
	}

	// public static enum ECostTranfer {
	// INVARIABLE, DELTA, UPDATE;
	// }

	public static enum EOptimizationStrategy {
		INCREASING, DECREASING, DICHOTOMIC;
	}

	// public static enum EDefaultCost {
	// ZERO, K, INTERMEDIATE;
	// }

	public static enum EExtension {
		V, A, VA, STR1, STR2, STR3, STR2S, STR1NEG, STR2NEG, STRCPRS, CT, CT2, MDD, MDDSHORT, GAC4, RPWC, RPWC2;
	}

	public enum EExtractionMethod {
		DEC_VAR, DEC_CON, VAR, CON, INC, INC_FIRST, MAX_CSP;
	}

	public static enum ELearningNogood {
		NO, RST, MIN_STD, RST_MIN, RST_SYM;

		public boolean isRstType() {
			return this == RST || this == RST_MIN || this == RST_SYM;
		}
	}

	public enum ELearningState {
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

	public static enum ERestartsMeasure {
		FAILED, WRONG, BACKTRACK, SOLUTION;
	}

	// public static enum EWCNConversion {
	// NO, NATURAL, RANDOM;
	// }

	public static enum EExport {
		NO,
		STD, // standard output stdout
		FILE
	}

	public static enum EExportMode {
		NO,
		INTENSION,
		EXTENSION, // EXTENSION is for automatic mode (either supports or conflicts)
		EXTENSION_SUPPORTS,
		EXTENSION_CONFLICTS;
	}

	public enum ESemantics {
		SUPPORTS, CONFLICTS, SOFT;
	}

	public enum ESingletonAssignment {
		ANY, FIRST, LAST;
	}

	public static enum EStopping {
		FULL_EXPLORATION, REACHED_GOAL, EXCEEDED_TIME;
	}

	public static enum ETypeOptimization {
		MINIMIZE, MAXIMIZE;
	}

	public static enum ESymmetryBreaking {
		NO,
		LE,
		LEX,
		LE_MERGED,
		LEX_MERGED,
		VAL, // VAL is not finalized
		REC;
	}

	public static enum EWeighting {
		VAR, UNIT, CACD, CHS;
	}

	public static enum EZip {
		NO, BZ2, GZIP, LZMA;

		public String compressCommand() {
			assert this != NO;
			return this == BZ2 ? "bz2 " : this == GZIP ? "gzip " : "lzma ";
		}

		public String decompressCommand() {
			assert this != NO;
			return this == BZ2 ? "bunzip2 " : this == GZIP ? "gunzip " : "lzma -d ";
		}

	}

	// public static NodeType getConstantFor(String name) {
	// return (NodeType) (Reflector.getControledFieldValueOfWithName(NodeType.class, name.toUpperCase())); }
}
