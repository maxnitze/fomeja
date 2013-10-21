package de.agra.sat.koselleck.decompiling.datatypes;

import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * 
 * @author Max Nitze
 */
public enum ConstraintOperator {
	EQUAL("==", "!=", "==", "if_[i]cmpeq", "if_[i]cmpne"),
	GREATER_EQUAL(">=", "<", "<=", "if_[i]cmpge", "if_[i]cmplt"),
	GREATER(">", "<=", "<", "if_[i]cmpgt", "if_[i]cmple"),
	LESS_EQUAL("<=", ">", ">=", "if_[i]cmple", "if_[i]cmpgt"),
	LESS("<", ">=", ">", "if_[i]cmplt", "if_[i]cmpge"),
	NOT_EQUAL("!=", "==", "!=", "if_[i]cmpne", "if_[i]cmpeq"),
	
	NULL("", "", "", "", "");
	
	/**  */
	public final String asciiName;
	/**  */
	public final String oppositeAsciiName;
	/**  */
	public final String swappedAsciiName;
	/**  */
	public final String opcode;
	/**  */
	public final String oppositeOpcode;
	
	/**
	 * 
	 * @param asciiName
	 * @param oppositeAsciiName
	 * @param swappedAsciiName
	 * @param opcode
	 * @param oppositeOpcode
	 */
	ConstraintOperator(String asciiName, String oppositeAsciiName, String swappedAsciiName, String opcode, String oppositeOpcode) {
		this.asciiName = asciiName;
		this.oppositeAsciiName = oppositeAsciiName;
		this.swappedAsciiName = swappedAsciiName;
		this.opcode = opcode;
		this.oppositeOpcode = oppositeOpcode;
	}
	
	/**
	 * 
	 * @param asciiName
	 * 
	 * @return
	 */
	public static ConstraintOperator fromAsciiName(String asciiName) {
		for(ConstraintOperator co : values())
			if(asciiName.equals(co.asciiName))
				return co;
		throw new IllegalArgumentException("no constant with ascii name \"" + asciiName + "\" found");
	}
	
	/**
	 * 
	 * @param oppositeAsciiName
	 * 
	 * @return
	 */
	public static ConstraintOperator fromOppositeAsciiName(String oppositeAsciiName) {
		for(ConstraintOperator co : values())
			if(oppositeAsciiName.equals(co.oppositeAsciiName))
				return co;
		throw new IllegalArgumentException("no constant with opposite ascii name \"" + oppositeAsciiName + "\" found");
	}
	
	/**
	 * 
	 * @param swappedAsciiName
	 * 
	 * @return
	 */
	public static ConstraintOperator fromSwappedAsciiName(String swappedAsciiName) {
		for(ConstraintOperator co : values())
			if(swappedAsciiName.equals(co.swappedAsciiName))
				return co;
		throw new IllegalArgumentException("no constant with swapped ascii name \"" + swappedAsciiName + "\" found");
	}
	
	/**
	 * 
	 * @param opcode
	 * 
	 * @return
	 */
	public static ConstraintOperator fromOpcode(String opcode) {
		for(ConstraintOperator co : values())
			if(opcode.matches(co.opcode))
				return co;
		throw new IllegalArgumentException("no constant with opcode \"" + opcode + "\" found");
	}
	
	/**
	 * 
	 * @param opcode
	 * 
	 * @return
	 */
	public static ConstraintOperator fromOpcode(Opcode opcode) {
		for(ConstraintOperator co : values())
			if(opcode.name.matches(co.opcode))
				return co;
		throw new IllegalArgumentException("no constant with opcode \"" + opcode + "\" found");
	}
	
	/**
	 * 
	 * @param oppositeOpcode
	 * 
	 * @return
	 */
	public static ConstraintOperator fromOppositeOpcode(String oppositeOpcode) {
		for(ConstraintOperator co : values())
			if(oppositeOpcode.matches(co.oppositeOpcode))
				return co;
		throw new IllegalArgumentException("no constant with opposite opcode \"" + oppositeOpcode + "\" found");
	}
	
	/**
	 * 
	 * @param oppositeOpcode
	 * 
	 * @return
	 */
	public static ConstraintOperator fromOppositeOpcode(Opcode oppositeOpcode) {
		for(ConstraintOperator co : values())
			if(oppositeOpcode.name.matches(co.oppositeOpcode))
				return co;
		throw new IllegalArgumentException("no constant with opposite opcode \"" + oppositeOpcode + "\" found");
	}
}
