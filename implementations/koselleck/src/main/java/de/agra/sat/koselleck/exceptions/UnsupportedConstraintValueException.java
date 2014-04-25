package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;

/**
 * UnsupportedConstraintValueException is a  runtime exception that is thrown
 *  when a unsupported abstract constraint value is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedConstraintValueException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -1690193560716283063L;

	/**
	 * Constructor for a new UnsupportedConstraintValueException.
	 * 
	 * @param constraintValue the unsupported abstract constraint value
	 */
	public UnsupportedConstraintValueException(AbstractConstraintValue constraintValue) {
		super("constraint value type \"" + (constraintValue == null ? "null" : constraintValue.getClass().getSimpleName()) + "\" is not supported");
	}
}
