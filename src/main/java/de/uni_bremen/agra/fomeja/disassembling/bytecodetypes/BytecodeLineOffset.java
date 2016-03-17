package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineOffset extends BytecodeLine {
	/** the value */
	private final int offset;

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

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public int getOffset() {
		return this.offset;
	}
}
