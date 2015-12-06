package de.agra.fomeja.disassembling.bytecodetypes;

import de.agra.fomeja.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public abstract class BytecodeLineConstantTable extends BytecodeLine {
	/** the constant table offset */
	private final int constantTableIndex;

	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param constantTableIndex
	 */
	public BytecodeLineConstantTable(String line, int lineNumber, Opcode opcode, int constantTableIndex) {
		super(line, lineNumber, opcode);

		this.constantTableIndex = constantTableIndex;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public int getConstantTableIndex() {
		return this.constantTableIndex;
	}
}
