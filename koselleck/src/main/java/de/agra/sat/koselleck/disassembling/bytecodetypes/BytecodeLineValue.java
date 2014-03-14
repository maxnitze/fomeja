package de.agra.sat.koselleck.disassembling.bytecodetypes;

import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineValue extends BytecodeLine {
	/** the value */
	public final Object value;
	
	/**
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param value
	 */
	public BytecodeLineValue(String line, int lineNumber, Opcode opcode, Object value) {
		super(line, lineNumber, opcode);
		
		this.value = value;
	}
}
