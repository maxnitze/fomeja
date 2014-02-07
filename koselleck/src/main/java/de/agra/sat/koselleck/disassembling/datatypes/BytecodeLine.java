package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * BytecodeLine represents a disassembled byte code line.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class BytecodeLine {
	/** types of bytecode lines */
	public enum BytecodeLineType {
		SIMPLE,
		VALUE,
		OFFSET,
		CONSTANT_TABLE_INDEX;
	}
	
	/** the trimmed line */
	public final String line;
	
	/** the number */
	public final int lineNumber;
	/** the opcode */
	public final Opcode opcode;
	/** the number of the following line */
	public final int followingLineNumber;
	
	/** the type */
	public final BytecodeLineType type;
	
	/**
	 * Constructor for a new byte code line.
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param followingLineNumber
	 * @param type
	 */
	public BytecodeLine(String line, int lineNumber, Opcode opcode, int followingLineNumber, BytecodeLineType type) {
		this.line = line;
		this.lineNumber = lineNumber;
		this.opcode = opcode;
		this.followingLineNumber = followingLineNumber;
		this.type = type;
	}
	
	/**
	 * toString returns a string representation of this byte code line.
	 * 
	 * @return a string representation of this byte code line
	 */
	@Override
	public String toString() {
		return this.line;
	}
}
