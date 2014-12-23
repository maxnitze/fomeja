package de.agra.sat.koselleck.exceptions;

/* imports */
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ParameterObjectException extends RuntimeException {
	/** COMMENT */
	private static final long serialVersionUID = -1204781754643644460L;

	/**
	 * COMMENT
	 * 
	 * @param parameterObject
	 * @param message
	 */
	public ParameterObjectException(ParameterObject parameterObject, String message) {
		super("\"" + parameterObject + "\": " + message);
	}
}
