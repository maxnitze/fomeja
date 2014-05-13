package de.agra.sat.koselleck.exceptions;

/**
 * UnsupportedNumberTypeException is a runtime exception that is thrown when a
 *  unsupported number type is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedComparableNumberTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -5546321011556996377L;

	/**
	 * Constructor for a new UnsupportedNumberTypeException.
	 * 
	 * @param number the unsupported comparable number
	 */
	public <T extends Number> UnsupportedComparableNumberTypeException(T number) {
		super("number type \"" + (number == null ? "null" : number.getClass().getSimpleName()) + "\" is not supported");
	}
}