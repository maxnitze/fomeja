package de.agra.sat.koselleck.exceptions;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class LiteralNotCastableException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -3500409810248938674L;

	/**
	 * COMMENT
	 * 
	 * @param message
	 */
	public LiteralNotCastableException(String message) {
		super(message);
	}
}
