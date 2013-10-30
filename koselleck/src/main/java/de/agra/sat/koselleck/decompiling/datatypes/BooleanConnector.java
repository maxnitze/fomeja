package de.agra.sat.koselleck.decompiling.datatypes;

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
}
