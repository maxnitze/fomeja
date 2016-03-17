package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineSimple extends BytecodeLine {
	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param type
	 */
	public BytecodeLineSimple(String line, int lineNumber, Opcode opcode) {
		super(line, lineNumber, opcode);
	}
}
