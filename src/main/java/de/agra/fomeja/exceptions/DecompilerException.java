package de.agra.fomeja.exceptions;

/**
 * DecompilerException COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class DecompilerException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -4967257961391231346L;

	/**
	 * COMMENT
	 * 
	 * @param message the message of the exception
	 */
	public DecompilerException(String message) {
		super(message);
	}
}
