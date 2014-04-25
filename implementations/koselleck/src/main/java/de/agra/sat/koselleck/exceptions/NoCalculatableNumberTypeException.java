package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;

/**
 * NoCalculatableNumberType is a runtime exception that is thrown if the
 *  abstract constraint literal has no comparable number type.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NoCalculatableNumberTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 1099976679067217712L;

	/**
	 * Constructor for a new NoCalculatableNumberType.
	 * 
	 * @param constraintLiteral the abstract constraint literal of the
	 *  exception
	 */
	public NoCalculatableNumberTypeException(AbstractConstraintLiteral<?> constraintLiteral) {
		super("abstract constraint literal \"" + constraintLiteral + "\" has no calculatable number type");
	}
}
