package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public enum BooleanConnector {
	AND("&&"),
	OR("||"),
	
	NULL("");
	
	/**  */
	public final String code;
	
	/**
	 * 
	 * @param code
	 */
	BooleanConnector(String code) {
		this.code = code;
	}
}
