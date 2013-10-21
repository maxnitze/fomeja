package de.agra.sat.koselleck.exceptions;

/**
 * 
 * @author Max Nitze
 */
public class UnsupportedNumberTypeException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -5546321011556996377L;

	/**
	 * 
	 * @param number
	 */
	public UnsupportedNumberTypeException(Number number) {
		super("number type \"" + (number == null ? "null" : number.getClass().getSimpleName()) + "\" is not supported");
	}
}
