package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class UnknownOpcodeException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = 6423663911509239448L;

	/**
	 * 
	 * @param opcode
	 */
	public UnknownOpcodeException(Opcode opcode) {
		super("Opcode " + (opcode == null ? "null" : "\"" + opcode.name() + "\"") + " is not known");
	}
}
