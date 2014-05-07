package de.agra.sat.koselleck.exceptions;

/**
 * MissformatedBytecodeLineException is a runtime exception that is thrown when
 *  a java byte code line was expected but the format of the given line did not
 *  fit the expected format.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class MissformattedBytecodeLineException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -6735928757307264346L;

	/**
	 * Constructor for a new MissformattedBytecodeLineException.
	 * 
	 * @param message the message of the exception
	 */
	public MissformattedBytecodeLineException(String message) {
		super(message);
	}
}
