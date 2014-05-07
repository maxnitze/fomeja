package de.agra.sat.koselleck.disassembling.bytecodetypes;

import de.agra.sat.koselleck.types.Opcode;

/**
 * BytecodeLine represents a disassembled byte code line.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class BytecodeLine {
	/** the trimmed line */
	public final String line;

	/** the number */
	public final int lineNumber;
	/** the opcode */
	public final Opcode opcode;
	/** the number of the following line */
	public final int followingLineNumber;

	/**
	 * Constructor for a new byte code line.
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 */
	public BytecodeLine(String line, int lineNumber, Opcode opcode) {
		this.line = line;
		this.lineNumber = lineNumber;
		this.opcode = opcode;
		this.followingLineNumber = lineNumber + opcode.followingLineOffset;
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
