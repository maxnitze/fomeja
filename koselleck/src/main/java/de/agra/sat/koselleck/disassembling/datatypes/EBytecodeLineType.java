package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public enum EBytecodeLineType {
	FIELD("Field"),
	METHOD("Method"),
	CLASS("class");
	
	/**  */
	private String name;
	
	/**
	 * 
	 * @param name
	 */
	EBytecodeLineType(String name) {
		this.name = name;
	}
	
	/**
	 * 
	 * @return
	 */
	public String getName() {
		return this.name;
	}
	
	/**
	 * 
	 * @param name
	 * 
	 * @return
	 */
	public static EBytecodeLineType fromString(String name) {
		for(EBytecodeLineType t : values())
			if(t.name.equals(name))
				return t;
		throw new IllegalArgumentException("no constant with name \"" + name + "\" found");
	}
}
