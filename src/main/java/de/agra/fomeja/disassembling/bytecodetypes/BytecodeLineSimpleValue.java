package de.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import de.agra.fomeja.types.Opcode;

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
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param value
	 */
	public BytecodeLineSimpleValue(String line, int lineNumber, Opcode opcode, Object value) {
		super(line, lineNumber, opcode);

		this.value = value;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Object getValue() {
		return this.value;
	}
}
