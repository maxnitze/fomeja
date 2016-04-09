package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineOffset extends BytecodeLine {
	/** the value */
	private final int offset;

	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 * @param offset COMMENT
	 */
	public BytecodeLineOffset(String line, int lineNumber, Opcode opcode, int offset) {
		super(line, lineNumber, opcode);

		this.offset = offset;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getOffset() {
		return this.offset;
	}
}
