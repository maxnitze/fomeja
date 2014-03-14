package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class PrefixedClass {
	/**  */
	public final Class<?> clazz;
	/** the opcode of the class */
	public final Opcode fieldCode;
	/** the value */
	public final int value;
	
	/**
	 * 
	 * @param clazz
	 * @param fieldCode
	 * @param value
	 */
	public PrefixedClass(Class<?> clazz, Opcode fieldCode, int value) {
		this.clazz = clazz;
		this.fieldCode = fieldCode;
		this.value = value;
	}
}
