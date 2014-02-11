package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineConstantTableClass extends BytecodeLineConstantTable {
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
		super(line, lineNumber, opcode, constantTableOffset);
		
		this.clazz = clazz;
	}
}
