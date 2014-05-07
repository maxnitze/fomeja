package de.agra.sat.koselleck.disassembling.bytecodetypes;

/** imports */
import java.util.HashMap;
import java.util.Map;

import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineTableswitch extends BytecodeLine {
	/** the constant table offset */
	public final Map<String, Integer> offsetsMap;

	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 */
	public BytecodeLineTableswitch(String line, int lineNumber, Opcode opcode) {
		super(line, lineNumber, opcode);

		this.offsetsMap = new HashMap<String, Integer>();
	}
}
