package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

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
