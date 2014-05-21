package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.backends.Dialect;

/**
 * UnsupportedDialectTypeException is a runtime exception that is thrown when a
 *  unsupported dialect type is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedDialectTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 928597192340482514L;

	/**
	 * Constructor for a new UnsupportedDialectTypeException.
	 * 
	 * @param dialect the unsupported dialect
	 * @param theoremProverString the name of the theorem prover
	 */
	public UnsupportedDialectTypeException(Dialect<?, ?> dialect, String theoremProverName) {
		super("the dialect type \"" + dialect.dialectType.name() + "\" is not supported by \"" + theoremProverName + "\".");
	}
}
