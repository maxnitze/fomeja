package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.util.HashMap;
import java.util.Map;

import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;

/**
 * BytecodeLine represents a disassembled byte code line.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class BytecodeLine {	
	/** the line */
	public final String line;
	
	/** the number of the line */
	public final int lineNumber;
	/** the opcode of the byte code line */
	public final Opcode opcode;
	/** the number of the next line */
	public final int followingLineNumber;
	/** the value of the byte code line */
	public final Integer value;
	/** the offset of the byte code  line */
	public final int offset;
	/** the constant table index of the byte code line */
	public final int constantTableIndex;
	/** the type of the byte code line */
	public final BytecodeLineType type;
	/** the map of offsets of a table switch */
	public final Map<String, Integer> switchOffsets;
	
	/**
	 * Constructor for a new byte code line.
	 * 
	 * @param componentClass the class of the current component
	 * @param line the line of the disassembled method
	 */
	public BytecodeLine(Class<?> componentClass, String line) {
		this.line = line.trim().replaceAll("\\s+", " ");
		
		if(!this.line.matches(BytecodeLineRegexes.opcode))
			throw new MissformattedBytecodeLineException("no line number or opcode given");
		
		this.lineNumber = Integer.parseInt(this.line.replaceAll(BytecodeLineRegexes.lineNumber, "${lineNumber}"));
		this.opcode = Opcode.fromString(this.line.replaceAll(BytecodeLineRegexes.opcode, "${opcode}"));
		this.followingLineNumber = this.lineNumber + this.opcode.followingLineOffset;
		
		if(this.line.matches(BytecodeLineRegexes.value)) {
			this.value = Integer.parseInt(this.line.replaceAll(BytecodeLineRegexes.value, "${value}"));
			this.offset = -1;
			this.constantTableIndex = -1;
			this.type = null;
			this.switchOffsets = null;
		} else if(this.line.matches(BytecodeLineRegexes.offset)) {
			this.value = -1;
			this.offset = Integer.parseInt(this.line.replaceAll(BytecodeLineRegexes.offset, "${offset}"));
			this.constantTableIndex = -1;
			this.type = null;
			this.switchOffsets = null;
		} else if(this.line.matches(BytecodeLineRegexes.constantTableIndex)) {
			this.value = -1;
			this.offset = -1;
			this.constantTableIndex = Integer.parseInt(this.line.replaceAll(BytecodeLineRegexes.constantTableIndex, "${index}"));
			this.type = new BytecodeLineType(componentClass, this.line);
			this.switchOffsets = null;
		} else if(this.line.matches(BytecodeLineRegexes.tableswitch)) {
			this.value = -1;
			this.offset = -1;
			this.constantTableIndex = -1;
			this.type = null;
			this.switchOffsets = new HashMap<String, Integer>();
		} else {
			this.offset = -1;
			this.constantTableIndex = -1;
			this.value = -1;
			this.type = null;
			this.switchOffsets = null;
		}
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
