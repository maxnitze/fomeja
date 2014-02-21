package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;

/**
 * An enumeration of the two boolean connectors && and ||.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum BooleanConnector {
	AND("&&"),
	OR("||");
	
	/** the code */
	public final String code;
	
	/**
	 * Constructor for a new boolean connector.
	 * 
	 * @param code the new code
	 */
	BooleanConnector(String code) {
		this.code = code;
	}
	
	/**
	 * 
	 * @return
	 */
	public BooleanConnector getOppositeConnector() {
		switch(this) {
		case AND:
			return OR;
		case OR:
			return AND;
		default:
			UnknownBooleanConnectorException unknownBooleanConnectorException = new UnknownBooleanConnectorException(this);
			Logger.getLogger(BooleanConnector.class).fatal(unknownBooleanConnectorException.getMessage());
			throw unknownBooleanConnectorException;
		}
	}
}
