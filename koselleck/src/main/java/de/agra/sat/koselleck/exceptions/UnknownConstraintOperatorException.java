package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintOperator;

/**
 * 
 * @author Max Nitze
 */
public class UnknownConstraintOperatorException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -2790223235115376867L;
	
	/**
	 * 
	 * @param operator
	 */
	public UnknownConstraintOperatorException(ConstraintOperator operator) {
		super("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
	}
}
