package de.agra.sat.koselleck.disassembling.bytecodetypes;

import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineOffset extends BytecodeLine {
	/** the value */
	public final int offset;
	
	/**
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param offset
	 */
	public BytecodeLineOffset(String line, int lineNumber, Opcode opcode, int offset) {
		super(line, lineNumber, opcode);
		
		this.offset = offset;
	}
}
