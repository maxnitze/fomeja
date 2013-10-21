package de.agra.sat.koselleck.exceptions;

/**
 * 
 * @author Max Nitze
 */
public class MissformattedBytecodeLineException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -6735928757307264346L;
	
	/**
	 * 
	 * @param message
	 */
	public MissformattedBytecodeLineException(String message) {
		super(message);
	}
}
