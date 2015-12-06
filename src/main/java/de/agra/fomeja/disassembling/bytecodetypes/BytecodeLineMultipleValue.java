package de.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import de.agra.fomeja.types.Opcode;

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
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param values
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
	 * @return
	 */
	public Object[] getValues() {
		return this.values;
	}
}
