package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineSimple extends BytecodeLine {
	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 */
	public BytecodeLineSimple(String line, int lineNumber, Opcode opcode) {
		super(line, lineNumber, opcode);
	}
}
