package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.lang.reflect.AccessibleObject;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineConstantTableAccessibleObject extends BytecodeLineConstantTable {
	/** the accessible object */
	public final AccessibleObject accessibleObject;
	
	
	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param constantTableOffset
	 * @param accessibleObject
	 */
	public BytecodeLineConstantTableAccessibleObject(String line, int lineNumber, Opcode opcode, int constantTableOffset, AccessibleObject accessibleObject) {
		super(line, lineNumber, opcode, constantTableOffset);
		
		this.accessibleObject = accessibleObject;
	}
}
