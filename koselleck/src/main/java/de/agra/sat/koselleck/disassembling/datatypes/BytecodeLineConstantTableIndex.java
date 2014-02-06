package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.lang.reflect.AccessibleObject;

/**
 * 
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineConstantTableIndex extends BytecodeLine {
	/** the constant table offset */
	public final int constantTableOffset;
	
	/** the accessible object */
	public final AccessibleObject accessibleObject;
	
	
	/**
	 * 
	 * 
	 * @param line
	 * @param lineNumber
	 * @param opcode
	 * @param followingLineNumber
	 * @param type
	 * @param constantTableOffset
	 * @param accessibleObject
	 */
	public BytecodeLineConstantTableIndex(String line, int lineNumber, Opcode opcode, int followingLineNumber, BytecodeLineType type, int constantTableOffset, AccessibleObject accessibleObject) {
		super(line, lineNumber, opcode, followingLineNumber, type);
		
		this.constantTableOffset = constantTableOffset;
		this.accessibleObject = accessibleObject;
	}
}
