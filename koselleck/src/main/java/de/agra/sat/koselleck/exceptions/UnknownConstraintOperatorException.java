package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintOperator;

/**
 * UnknownConstraintOperator is a runtime exception that is thrown when an
 *  unknown constraint operator is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnknownConstraintOperatorException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -2790223235115376867L;
	
	/**
	 * Constructor for a new UnknownConstraintOperatorException.
	 * 
	 * @param operator the unknown constraint operator
	 */
	public UnknownConstraintOperatorException(ConstraintOperator operator) {
		super("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
	}
}
