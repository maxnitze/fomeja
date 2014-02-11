package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public abstract class BytecodeLineConstantTable extends BytecodeLine {
	/** the constant table offset */
	public final int constantTableIndex;
	
	
	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param constantTableIndex
	 */
	public BytecodeLineConstantTable(String line, int lineNumber, Opcode opcode, int constantTableIndex) {
		super(line, lineNumber, opcode);
		
		this.constantTableIndex = constantTableIndex;
	}
}
