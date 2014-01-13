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
	
	/**
	 * 
	 * @param clazz
	 * @param fieldCode
	 */
	public PrefixedClass(Class<?> clazz, Opcode fieldCode) {
		this.clazz = clazz;
		this.fieldCode = fieldCode;
	}
}
