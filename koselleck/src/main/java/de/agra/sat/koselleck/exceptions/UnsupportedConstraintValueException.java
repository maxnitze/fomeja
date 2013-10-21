package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintValue;

/**
 * 
 * @author Max Nitze
 */
public class UnsupportedConstraintValueException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -1690193560716283063L;

	/**
	 * 
	 * @param constraintValue
	 */
	public UnsupportedConstraintValueException(AbstractConstraintValue constraintValue) {
		super("constraint value type \"" + (constraintValue == null ? "null" : constraintValue.getClass().getSimpleName()) + "\" is not supported");
	}
}
