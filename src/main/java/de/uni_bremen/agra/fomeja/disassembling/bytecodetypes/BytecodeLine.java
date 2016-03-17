package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * BytecodeLine represents a disassembled byte code line.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class BytecodeLine {
	/** the trimmed line */
	private final String line;

	/** the number */
	private final int lineNumber;
	/** the opcode */
	private final Opcode opcode;
	/** the number of the following line */
	private final int followingLineNumber;

	/**
	 * Constructor for a new byte code line.
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 */
	public BytecodeLine(String line, int lineNumber, Opcode opcode) {
		this.line = line;
		this.lineNumber = lineNumber;
		this.opcode = opcode;
		this.followingLineNumber = lineNumber + opcode.getFollowingLineOffset();
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getLine() {
		return this.line;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getLineNumber() {
		return this.lineNumber;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Opcode getOpcode() {
		return this.opcode;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getFollowingLineNumber() {
		return this.followingLineNumber;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

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
