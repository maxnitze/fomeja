package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineMultipleValue extends BytecodeLine {
	/** the value */
	private final Object[] values;

	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 * @param values COMMENT
	 */
	public BytecodeLineMultipleValue(String line, int lineNumber, Opcode opcode, Object[] values) {
		super(line, lineNumber, opcode);

		this.values = values;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Object[] getValues() {
		return this.values;
	}
}
