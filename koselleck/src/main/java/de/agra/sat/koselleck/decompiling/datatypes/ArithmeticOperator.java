package de.agra.sat.koselleck.decompiling.datatypes;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.disassembling.datatypes.Opcode;
import de.agra.sat.koselleck.exceptions.UnknownOpcodeException;
/** imports */

/**
 * An enumeration of the four arithmetic operators +, -, * and /.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ArithmeticOperator {
	ADD("+"),
	SUB("-"),
	MUL("*"),
	DIV("/");
	
	/** the ascii name */
	public final String asciiName;
	
	/**
	 * Constructor for a new arithmetic operator.
	 * 
	 * @param asciiName the new ascii name
	 */
	ArithmeticOperator(String asciiName) {
		this.asciiName = asciiName;
	}
	
	/**
	 * fromOpcode returns the corresponding arithmetic operator for the
	 *  arithmetic opcodes.
	 * 
	 * @param opcode the arithmetic opcode
	 * 
	 * @return the arithmetic operator corresponding to the arithmetic opcode
	 */
	public static ArithmeticOperator fromOpcode(Opcode opcode) {
		switch(opcode){
		case add:
			return ADD;
		case sub:
			return SUB;
		case mul:
			return MUL;
		case div:
			return DIV;
		default:
			UnknownOpcodeException exception = new UnknownOpcodeException(opcode);
			Logger.getLogger(ArithmeticOperator.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
