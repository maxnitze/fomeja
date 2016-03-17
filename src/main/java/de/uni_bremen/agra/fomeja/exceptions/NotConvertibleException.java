package de.uni_bremen.agra.fomeja.exceptions;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NotConvertibleException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 3630993355082521881L;

	/**
	 * COMMENT
	 * 
	 * @param message
	 */
	public NotConvertibleException(String message) {
		super(message);
	}
}
