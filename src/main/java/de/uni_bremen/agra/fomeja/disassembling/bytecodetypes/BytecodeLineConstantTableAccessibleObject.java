package de.uni_bremen.agra.fomeja.disassembling.bytecodetypes;

/* imports */
import java.lang.reflect.AccessibleObject;

import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public class BytecodeLineConstantTableAccessibleObject extends BytecodeLineConstantTable {
	/** the accessible object */
	private final AccessibleObject accessibleObject;

	/**
	 * COMMENT
	 * 
	 * @param line COMMENT
	 * @param lineNumber COMMENT
	 * @param opcode COMMENT
	 * @param constantTableOffset COMMENT
	 * @param accessibleObject COMMENT
	 */
	public BytecodeLineConstantTableAccessibleObject(String line, int lineNumber, Opcode opcode, int constantTableOffset, AccessibleObject accessibleObject) {
		super(line, lineNumber, opcode, constantTableOffset);

		this.accessibleObject = accessibleObject;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public AccessibleObject getAccessibleObject() {
		return this.accessibleObject;
	}
}
