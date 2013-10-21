package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.util.HashMap;
import java.util.Map;

import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;

/**
 * 
 * @author Max Nitze
 */
public class BytecodeLine {	
	/**  */
	public final String line;
	
	/**  */
	public final int lineNumber;
	/**  */
	public final Opcode opcode;
	/**  */
	public final int followingLineNumber;
	/**  */
	public final int value;
	/**  */
	public final int offset;
	/**  */
	public final int constantTableIndex;
	/**  */
	public final BytecodeLineType type;
	/**  */
	public final Map<String, Integer> switchOffsets;
	
	/**
	 * 
	 * @param line
	 */
	public BytecodeLine(Object component, String line) {
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
			this.type = new BytecodeLineType(component, this.line);
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
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		return this.line;
	}
}
