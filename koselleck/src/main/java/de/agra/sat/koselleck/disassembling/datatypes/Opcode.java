package de.agra.sat.koselleck.disassembling.datatypes;

import org.apache.log4j.Logger;

/**
 * 
 * @author Max Nitze
 */
public enum Opcode {
	aload_0("aload_0", 1, "^aload_0$", OpcodeType.VALUE, "aload_"),
	aload("aload", 1, "^aload(_[1-5])?$", OpcodeType.VALUE, "aload(_|\\s)"),
	
	iconst("iconst", 1, "^iconst_\\d+$", OpcodeType.VALUE, "iconst_"),
	bipush("bipush", 2, "^bipush$", OpcodeType.VALUE, "bipush\\s"),
	
	getfield("getfield", 3, "^getfield$", OpcodeType.CONSTANT_TABLE_INDEX, "getfield"),
	getstatic("getstatic", 3, "^getstatic$", OpcodeType.CONSTANT_TABLE_INDEX, "getstatic"),
	
	checkcast("checkcast", 3, "^checkcast$", OpcodeType.CONSTANT_TABLE_INDEX, "checkcast"),
	
	add("add", 1, "^[i]add$", null, ""),
	sub("sub", 1, "^[i]sub$", null, ""),
	mul("mul", 1, "^[i]mul$", null, ""),
	div("div", 1, "^[i]div$", null, ""),
	
	invokevirtual("invokevirtual", 3, "^invokevirtual$", null, ""),
	
	tableswitch("tableswitch", 0, "^tableswitch$", OpcodeType.SWITCH, "tableswitch"),
	
	_goto("goto", 1, "^goto$", null, ""),

	iload("iload", 1, "^iload(_\\d+)?$", OpcodeType.VALUE, "iload(_|\\s)"),
	istore("istore", 1, "^istore(_\\d+)?$", OpcodeType.VALUE, "istore(_|\\s)"),
	
	ifeq("ifeq", 3, "^ifeq$", OpcodeType.OFFSET, "ifeq"),							/** jump if zero */
	ifne("ifne", 3, "^ifne$", OpcodeType.OFFSET, "ifne"),							/** jump if nonzero */
	
	if_icmpeq("if_icmpeq", 3, "^if_icmpeq$", OpcodeType.OFFSET, "if_icmpeq"),		/** equal */
	if_icmpge("if_icmpge", 3, "^if_icmpge$", OpcodeType.OFFSET, "if_icmpge"),		/** greater-equal */
	if_icmpgt("if_icmpgt", 3, "^if_icmpgt$", OpcodeType.OFFSET, "if_icmpgt"),		/** greater */
	if_icmple("if_icmple", 3, "^if_icmple$", OpcodeType.OFFSET, "if_icmple"),		/** less-equal */
	if_icmplt("if_icmplt", 3, "^if_icmplt$", OpcodeType.OFFSET, "if_icmplt"),		/** less */
	if_icmpne("if_icmpne", 3, "^if_icmpne$", OpcodeType.OFFSET, "if_icmpne"),		/** not equal */
	
	ireturn("ireturn", 1, "^ireturn$", null, "");
	
	/**  */
	private enum OpcodeType { VALUE, OFFSET, CONSTANT_TABLE_INDEX, SWITCH };
	
	/**  */
	public final String name;
	/**  */
	public final int followingLineOffset;
	/**  */
	public final String opcodeRegex;
	/**  */
	private final OpcodeType type;
	/**  */
	private final String typeRegex;
	
	/**
	 * 
	 * @param name
	 * @param followingLineOffset
	 * @param opcodeRegex
	 * @param type
	 * @param typeRegex
	 */
	Opcode(String name, int followingLineOffset, String opcodeRegex, OpcodeType type, String typeRegex) {
		this.name= name;
		this.followingLineOffset = followingLineOffset;
		this.opcodeRegex = opcodeRegex;
		this.type = type;
		this.typeRegex = typeRegex;
	}
	
	/**
	 * 
	 * @param opcode
	 * 
	 * @return
	 */
	public static Opcode fromString(String opcode) {
		for(Opcode oc : values())
			if(opcode.matches(oc.opcodeRegex))
				return oc;
		Logger.getLogger(Opcode.class).fatal("no opcode matching \"" + opcode + "\"");
		throw new IllegalArgumentException("no opcode matching \"" + opcode + "\"");
	}
	
	/**
	 * 
	 * @return
	 */
	public static String getValueTypeGroup() {
		StringBuilder valueTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.VALUE) {
				if(valueTypeGroup.length() > 0)
					valueTypeGroup.append("|");
				valueTypeGroup.append(opcode.typeRegex);
			}
		}
		return valueTypeGroup.toString();
	}
	
	/**
	 * 
	 * @return
	 */
	public static String getOffsetTypeGroup() {
		StringBuilder valueTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.OFFSET) {
				if(valueTypeGroup.length() > 0)
					valueTypeGroup.append("|");
				valueTypeGroup.append(opcode.typeRegex);
			}
		}
		return valueTypeGroup.toString();
	}
	
	/**
	 * 
	 * @return
	 */
	public static String getConstantTableIndexTypeGroup() {
		StringBuilder valueTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.CONSTANT_TABLE_INDEX) {
				if(valueTypeGroup.length() > 0)
					valueTypeGroup.append("|");
				valueTypeGroup.append(opcode.typeRegex);
			}
		}
		return valueTypeGroup.toString();
	}
	
	/**
	 * 
	 * @return
	 */
	public static String getConstantSwitchGroup() {
		StringBuilder valueTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.SWITCH) {
				if(valueTypeGroup.length() > 0)
					valueTypeGroup.append("|");
				valueTypeGroup.append(opcode.typeRegex);
			}
		}
		return valueTypeGroup.toString();
	}
}
