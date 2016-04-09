package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
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
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 * @param constantTableOffset COMMENT
	 * @param type COMMENT
	 */
	public BytecodeLineConstantTableClass(String line, int lineNumber, Opcode opcode, int constantTableOffset, Class<?> type) {
		super(line, lineNumber, opcode, constantTableOffset);

		this.type = type;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Class<?> getType() {
		return this.type;
	}
}
