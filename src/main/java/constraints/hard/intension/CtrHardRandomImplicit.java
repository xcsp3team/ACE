/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.intension;

import java.security.MessageDigest;
import java.util.Arrays;

import constraints.Constraint;
import interfaces.TagUnsymmetric;
import problem.Problem;
import variables.Variable;

/**
 * This class denote any random constraint defined implicitly. For more information, see [Lecoutre, Boussemart et Hemery, 2003, Implicit random CSPs].
 * All supports (allowed tuples) or all conflicts (disallowed tuples) are not recorded in a list but computed when necessary. Note that indexes of
 * values and values match.
 */
public final class CtrHardRandomImplicit extends Constraint implements TagUnsymmetric {
	@Override
	public final boolean checkValues(int[] t) {
		return Arrays.equals(requiredSupport, t) ? true : implicitRandomList.randomByteFor(t) >= tightness;
	}

	/**
	 * This class allows managing implicit lists of random values. Using two fixed prefixes, it is possible to associate a random byte value with any
	 * tuple of a given fixed length. Different prefixes entail different behaviors. This technique uses a hash function like SHA or MD5.
	 */
	public static class RandomGenerationImplicit {
		/**
		 * The message digest algorithm.
		 */
		private final MessageDigest md;

		/**
		 * Array used to store the message.
		 */
		private final byte[] bytes;

		/**
		 * Builds a <code> ImplicitRandomList </code>
		 * 
		 * @param prefix1
		 *            the first prefix
		 * @param prefix2
		 *            the second prefix
		 * @param arity
		 *            the length of the tuples
		 * @param algorithm
		 *            the name of the message digest algorithm
		 */
		public RandomGenerationImplicit(int prefix1, int prefix2, int arity, String algorithm) {
			this.bytes = new byte[arity + 3];
			// two bytes of the first prefix are fixed
			short s = (short) prefix1;
			bytes[arity + 1] = (byte) (s & 0x00FF);
			bytes[arity] = (byte) (s >> 8);
			// one byte of the second prefix is fixed
			s = (short) prefix2;
			// bytes[length+3]= (byte)(s & 0x00FF);
			bytes[arity + 2] = (byte) (s & 0x00FF);
			try {
				this.md = MessageDigest.getInstance(algorithm);
			} catch (Exception e) {
				throw new IllegalArgumentException();
			}
		}

		/**
		 * Returns a random byte value from the given tuple.
		 * 
		 * @param tuple
		 *            a given tuple
		 * @return a random byte value from the given tuple
		 */
		public final byte randomByteFor(int[] tuple) {
			assert tuple.length + 3 == bytes.length;
			for (int i = 0; i < tuple.length; i++)
				bytes[i] = (byte) (tuple[i] & 0x000000FF);
			byte[] digest = md.digest(bytes);
			byte resultat = digest[0];
			for (int i = 1; i < digest.length; i++)
				resultat = (byte) (resultat ^ digest[i]);
			return resultat; // + 128) / 255.0;
		}

	}

	/**
	 * The implicit list of random tuples.
	 */
	private RandomGenerationImplicit implicitRandomList;

	/**
	 * The tightness of the constraint. It is a value ranging from <code>-128</code> to <code>127</code>. So, it is equivalent to a value ranging from
	 * <code>0</code> to <code>255</code>.
	 */
	private final byte tightness;

	/**
	 * The tuple that is, if not <code> null </code>, required as a support.
	 */
	private final int[] requiredSupport;

	/**
	 * Builds an <code> ImplicitRandomConstraint </code> object.
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached.
	 * @param scp
	 *            the variables involved in the constraint.
	 * @param tightness
	 *            the tightness of the constraint ; it is a value ranging from <code>-128</code> to <code>127</code> and so, it is equivalent to a
	 *            value ranging from <code>0</code> to <code>255</code>.
	 * @param instanceNumber
	 *            the number of the instance.
	 * @param algorithm
	 *            the name of the message digest algorithm that will be used for determining if a tuple is a support or a conflict.
	 * @param requiredSupport
	 *            a particular tuple which, if not <code> null </code>, must be considered as a support.
	 */
	public CtrHardRandomImplicit(Problem pb, Variable[] scp, byte tightness, int instanceNumber, String algorithm, int[] requiredSupport) {
		super(pb, scp);
		this.tightness = tightness;
		this.requiredSupport = requiredSupport != null ? (int[]) requiredSupport.clone() : null;
		this.implicitRandomList = new RandomGenerationImplicit(pb.stuff.collectedCtrsAtInit.size(), instanceNumber, scp.length, algorithm);
	}

	/**
	 * Builds an <code> ImplicitRandomConstraint </code> object.
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached.
	 * @param scp
	 *            the variables involved in the constraint.
	 * @param tightness
	 *            the tightness of the constraint ; it is a value ranging from <code>-128</code> to <code>127</code> and so, it is equivalent to a
	 *            value ranging from <code>0</code> to <code>255</code>.
	 * @param instanceNumber
	 *            the number of the instance.
	 * @param algorithm
	 *            the name of the message digest algorithm that will be used for determining if a tuple is a support or a conflict.
	 */
	public CtrHardRandomImplicit(Problem pb, Variable[] scp, byte tightness, int instanceNumber, String algorithm) {
		this(pb, scp, tightness, instanceNumber, algorithm, null);
	}

}
