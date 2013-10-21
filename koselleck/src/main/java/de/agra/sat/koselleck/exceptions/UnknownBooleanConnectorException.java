package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.BooleanConnector;

/**
 * 
 * @author Max Nitze
 */
public class UnknownBooleanConnectorException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -3106570633706852303L;
	
	/**
	 * 
	 * @param connector
	 */
	public UnknownBooleanConnectorException(BooleanConnector connector) {
		super("boolean connector " + (connector == null ? "null" : "\"" + connector.code + "\"") + " is not known");
	}
}
