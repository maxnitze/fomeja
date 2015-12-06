package de.agra.fomeja.disassembling.bytecodetypes;

/** imports */
import de.agra.fomeja.types.Opcode;

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
	 * @param line
	 * @param lineNumber
	 * @param opcode
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
	 * 
	 * @return
	 */
	public String getLine() {
		return this.line;
	}

	/**
	 * 
	 * @return
	 */
	public int getLineNumber() {
		return this.lineNumber;
	}

	/**
	 * 
	 * @return
	 */
	public Opcode getOpcode() {
		return this.opcode;
	}

	/**
	 * 
	 * @return
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
