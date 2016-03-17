package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineConstantTableClass extends BytecodeLineConstantTable {
	/** the accessible object */
	private final Class<?> type;

	/**
	 * COMMENT
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param constantTableOffset
	 * @param type
	 */
	public BytecodeLineConstantTableClass(String line, int lineNumber, Opcode opcode, int constantTableOffset, Class<?> type) {
		super(line, lineNumber, opcode, constantTableOffset);

		this.type = type;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public Class<?> getType() {
		return this.type;
	}
}
