package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineConstantTableClass extends BytecodeLine {
	/** the constant table offset */
	public final int constantTableOffset;
	
	/** the accessible object */
	public final Class<?> clazz;
	
	
	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param constantTableOffset
	 * @param clazz
	 */
	public BytecodeLineConstantTableClass(String line, int lineNumber, Opcode opcode, int constantTableOffset, Class<?> clazz) {
		super(line, lineNumber, opcode, BytecodeLineType.CONSTANT_TABLE_CLASS);
		
		this.constantTableOffset = constantTableOffset;
		this.clazz = clazz;
	}
}
