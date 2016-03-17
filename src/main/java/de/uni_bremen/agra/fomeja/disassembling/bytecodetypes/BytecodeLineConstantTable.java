package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public abstract class BytecodeLineConstantTable extends BytecodeLine {
	/** the constant table offset */
	private final int constantTableIndex;

	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 * @param constantTableIndex COMMENT
	 */
	public BytecodeLineConstantTable(String line, int lineNumber, Opcode opcode, int constantTableIndex) {
		super(line, lineNumber, opcode);

		this.constantTableIndex = constantTableIndex;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getConstantTableIndex() {
		return this.constantTableIndex;
	}
}
