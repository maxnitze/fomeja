package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.types.Opcode;

/**
 * UnknownOpcodeException is a runtime exception that is thrown when an unknown
 *  opcode is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnknownOpcodeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 6423663911509239448L;

	/**
	 * Constructor for a new UnknownOpcodeException.
	 * 
	 * @param opcode the unknown opcode
	 */
	public UnknownOpcodeException(Opcode opcode) {
		super("Opcode " + (opcode == null ? "null" : "\"" + opcode.name() + "\"") + " is not known");
	}
}
