package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineSimple extends BytecodeLine {
	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param followingLineNumber
	 * @param type
	 */
	public BytecodeLineSimple(String line, int lineNumber, Opcode opcode, int followingLineNumber, BytecodeLineType type) {
		super(line, lineNumber, opcode, followingLineNumber, type);
	}
}
