package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.Map;
import java.util.Set;

import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;

/**
 * AbstractConstraint is an abstract class for all types of constraints.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AbstractConstraint implements Cloneable {
	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * replaceAll replaces all occurrences of the string {@code regex} with the
	 *  replacement string {@code replacement}.
	 * 
	 * @param regex the string to replace
	 * @param replacement the replacement
	 */
	public abstract void replaceAll(String regex, String replacement);

	/**
	 * evaluate evaluates the abstract constraint.
	 * 
	 * @return the evaluated abstract constraint
	 */
	public abstract AbstractConstraint evaluate();

	/**
	 * substitute substitutes the abstract constraint with the given objects
	 *  (method parameters).
	 * 
	 * @param constraintArguments the arguments to substitute the constraint
	 *  with
	 */
	public abstract void substitute(Map<Integer, Object> constraintArguments);

	/**
	 * matches checks if any part of this abstract constraint matches the
	 *  string {@code regex}.
	 * 
	 * @param regex the string to check for
	 * 
	 * @return {@code true} if the abstract constraint contains the string
	 *  {@code regex}, {@code false} otherwise
	 */
	public abstract boolean matches(String regex);

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals();

	/**
	 * equals checks if this abstract constraint and the given object are
	 *  equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object an this abstract constraint are
	 *  equal, {@code false} otherwise
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * clone returns a copy of this abstract constraint.
	 * 
	 * @return a copy of this abstract constraint
	 */
	@Override
	public abstract AbstractConstraint clone();

	/**
	 * toString returns a string representation of this abstract constraint.
	 * 
	 * @return the string representation of this abstract constraint
	 */
	@Override
	public abstract String toString();
}
