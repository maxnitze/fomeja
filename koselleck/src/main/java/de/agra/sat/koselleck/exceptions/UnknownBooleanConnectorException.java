package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.BooleanConnector;

/**
 * UnknownBooleanConnectorException is a runtime exception that is thrown when
 *  an unknown boolean connector is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnknownBooleanConnectorException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -3106570633706852303L;
	
	/**
	 * Constructor for a new UnknownBooleanConnectorException.
	 * 
	 * @param connector the unknown boolean connector
	 */
	public UnknownBooleanConnectorException(BooleanConnector connector) {
		super("boolean connector " + (connector == null ? "null" : "\"" + connector.code + "\"") + " is not known");
	}
}
