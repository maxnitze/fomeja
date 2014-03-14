package de.agra.sat.koselleck.exceptions;

/**
 * UnsupportedVariableTypeException is a runtime exception that is thrown when a
 *  unsupported variable type is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedVariableTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 2044622315122396354L;

	/**
	 * Constructor for a new UnsupportedVariableTypeException.
	 * 
	 * @param type the unsupported type
	 */
	public UnsupportedVariableTypeException(String type) {
		super("variable type \"" + type + "\" is not supported");
	}
}
