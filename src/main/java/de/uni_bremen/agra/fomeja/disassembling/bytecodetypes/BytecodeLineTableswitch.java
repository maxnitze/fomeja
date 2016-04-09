package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

import java.util.HashMap;
import java.util.Map;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineTableswitch extends BytecodeLine {
	/** the constant table offset */
	private final Map<String, Integer> offsetsMap;

	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 */
	public BytecodeLineTableswitch(String line, int lineNumber, Opcode opcode) {
		super(line, lineNumber, opcode);

		this.offsetsMap = new HashMap<String, Integer>();
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Map<String, Integer> getOffsetsMap() {
		return this.offsetsMap;
	}
}
