package de.agra.sat.koselleck.decompiling.constrainttypes;

import de.agra.sat.koselleck.types.ArithmeticOperator;


/**
 * AbstractConstraintLiteral represents a literal in a constraint value.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AbstractConstraintLiteral<T> extends AbstractConstraintValue {
	/** the value of the literal */
	public final T value;

	/** flag if the value is variable */
	public final boolean isVariable;

	/** flag that indicates if the value is a number type */
	public final boolean isNumberType;

	/** flag that indicates if the value is a finished type */
	public final boolean isFinishedType;

	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param value the new value for the literal
	 * @param isVariable the new variable flag for the value
	 * @param isNumberType the new number type flag for the value
	 * @param isFinishedType the new finished type flag for the value
	 */
	public AbstractConstraintLiteral(T value, boolean isVariable, boolean isNumberType, boolean isFinishedType) {
		this.value = value;

		this.isVariable = isVariable;
		this.isNumberType = isNumberType;
		this.isFinishedType = isFinishedType;
	}

	/**
	 * replaceAll replaces all occurrences of the given regular expression
	 *  {@code regex} with the given {@code replacement}. if the replacement is
	 *  an integer type the type of this literal is changed to integer.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the replacement
	 */
	@Override
	public abstract void replaceAll(String regex, String replacement);

	/**
	 * If the value of the literal is parsable to integer evaluate parses it.
	 *  Afterwards this abstract constraint literal is returned.
	 * 
	 * @return this abstract constraint literal
	 */
	@Override
	public abstract AbstractConstraintValue evaluate();

	/**
	 * matches checks whether the value matches the given regular expression
	 *  {@code regex}.
	 * 
	 * @param regex the regular expression to look for
	 * 
	 * @return {@code true} if the value matches the given regular expression,
	 *  {@code false} otherwise
	 */
	@Override
	public abstract boolean matches(String regex);

	/**
	 * equals checks if this abstract constraint literal and the given object
	 *  are equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object an this abstract constraint
	 *  literal are equal, {@code false} otherwise
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * clone returns a copy of this abstract constraint literal.
	 * 
	 * @return a copy of this abstract constraint literal
	 */
	@Override
	public abstract AbstractConstraintLiteral<T> clone();

	/**
	 * toString returns the string representation of this abstract constraint
	 *  literal.
	 * 
	 * @return the string representation of this abstract constraint literal
	 */
	@Override
	public abstract String toString();

	/**
	 * 
	 * @param constraintLiteral
	 * 
	 * @return
	 */
	public abstract int compareTo(AbstractConstraintLiteral<?> constraintLiteral);

	/**
	 * 
	 * @param constraintLiteral
	 * 
	 * @return
	 */
	public abstract AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator);
}
