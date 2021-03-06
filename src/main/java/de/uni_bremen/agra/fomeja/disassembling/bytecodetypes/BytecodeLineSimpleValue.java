package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineSimpleValue extends BytecodeLine {
	/** the value */
	private final Object value;

	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 * @param value COMMENT
	 */
	public BytecodeLineSimpleValue(String line, int lineNumber, Opcode opcode, Object value) {
		super(line, lineNumber, opcode);

		this.value = value;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Object getValue() {
		return this.value;
	}
}
