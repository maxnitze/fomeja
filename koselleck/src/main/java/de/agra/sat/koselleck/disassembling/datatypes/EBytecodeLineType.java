package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * EBytecodeLineType is an enumeration of the different types a byte code line
 *  could describe.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum EBytecodeLineType {
	FIELD("Field"),
	METHOD("Method"),
	CLASS("class");
	
	/** the name */
	public final String name;
	
	/**
	 * Constructor for a new byte code line type enumeration element.
	 * 
	 * @param name the new name
	 */
	EBytecodeLineType(String name) {
		this.name = name;
	}
	
	/**
	 * fromString returns the byte code line type enumeration element thats
	 *  name equals the given name or an IllegalArgumentException if there is
	 *  no such element.
	 * 
	 * @param name the name to return the byte code line type enumeration
	 *  element to
	 * 
	 * @return the byte code line type enumeration element thats name equals
	 *  the given name, or an Illegal Argument Exception if there is no such
	 *  element
	 */
	public static EBytecodeLineType fromString(String name) {
		for(EBytecodeLineType t : values())
			if(t.name.equals(name))
				return t;
		throw new IllegalArgumentException("no constant with name \"" + name + "\" found");
	}
}
