package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineValue extends BytecodeLine {
	/** the value */
	public final Object value;
	
	/**
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param followingLineNumber
	 * @param type
	 * @param value
	 */
	public BytecodeLineValue(String line, int lineNumber, Opcode opcode, int followingLineNumber, BytecodeLineType type, Object value) {
		super(line, lineNumber, opcode, followingLineNumber, type);
		
		this.value = value;
	}
}
