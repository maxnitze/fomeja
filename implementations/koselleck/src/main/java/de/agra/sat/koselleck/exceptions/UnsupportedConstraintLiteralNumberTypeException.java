package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;

/**
 * UnsupportedNumberTypeException is a runtime exception that is thrown when a
 *  unsupported number type is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedConstraintLiteralNumberTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -1690263143250735011L;

	/**
	 * Constructor for a new UnsupportedConstraintLiteralNumberTypeException.
	 * 
	 * @param number the unsupported comparable number
	 */
	public UnsupportedConstraintLiteralNumberTypeException(@SuppressWarnings("rawtypes") Class<? extends AbstractConstraintLiteral> type) {
		super("constraint literal number type \"" + (type == null ? "null" : type.getSimpleName()) + "\" is not supported");
	}
}
