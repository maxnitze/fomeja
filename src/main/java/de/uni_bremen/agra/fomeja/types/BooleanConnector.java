package de.uni_bremen.agra.fomeja.types;

/* imports */
import org.apache.log4j.Logger;

/**
 * An enumeration of the two boolean connectors AND and OR.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum BooleanConnector {
	AND("&&"),
	OR("||");

	/** the code */
	private final String code;

	/**
	 * Constructor for a new boolean connector.
	 * 
	 * @param code the new code
	 */
	BooleanConnector(String code) {
		this.code = code;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return COMMENT
	 */
	public String getCode() {
		return this.code;
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return COMMENT
	 */
	public BooleanConnector getOppositeConnector() {
		switch(this) {
		case AND:
			return OR;
		case OR:
			return AND;
		default:
			String message = "constraint operator " + this.code + "\" is not known";
			Logger.getLogger(BooleanConnector.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}
}
