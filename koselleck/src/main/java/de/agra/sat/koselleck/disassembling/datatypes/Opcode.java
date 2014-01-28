package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import org.apache.log4j.Logger;

/**
 * Opcode is an enumeration of all used opcodes that occur in the byte code
 *  lines (needs to be extended for new data types or functionalities).
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum Opcode {
	aload_0("aload_0", 1, "^aload_0$", OpcodeType.VALUE, "aload_"),
	aload("aload", 1, "^aload(_[1-5])?$", OpcodeType.VALUE, "aload(_|\\s)"),

	bconst("bconst", 1, "^bconst(_\\d+)?$", OpcodeType.VALUE, "bconst(_|\\s)"),
	fconst("fconst", 1, "^fconst(_\\d+)?$", OpcodeType.VALUE, "fconst(_|\\s)"),
	iconst("iconst", 1, "^iconst(_\\d+)?$", OpcodeType.VALUE, "iconst(_|\\s)"),
	bipush("bipush", 2, "^bipush$", OpcodeType.VALUE, "bipush\\s"),
	
	getfield("getfield", 3, "^getfield$", OpcodeType.CONSTANT_TABLE_INDEX, "getfield"),
	getstatic("getstatic", 3, "^getstatic$", OpcodeType.CONSTANT_TABLE_INDEX, "getstatic"),
	
	checkcast("checkcast", 3, "^checkcast$", OpcodeType.CONSTANT_TABLE_INDEX, "checkcast"),
	
	i2d("i2d", 1, "^i2d$", null, ""),
	
	ldc2_w("ldc2_w", 3, "^ldc2_w$", OpcodeType.CONSTANT_TABLE_INDEX, "ldc2_w"),
	
	add("add", 1, "^[i|d]add$", null, ""),
	sub("sub", 1, "^[i|d]sub$", null, ""),
	mul("mul", 1, "^[i|d]mul$", null, ""),
	div("div", 1, "^[i|d]div$", null, ""),
	
	invokestatic("invokestatic", 3, "^invokestatic$", OpcodeType.CONSTANT_TABLE_INDEX, "invokestatic"),
	invokevirtual("invokevirtual", 3, "^invokevirtual$", OpcodeType.CONSTANT_TABLE_INDEX, "invokevirtual"),
	
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
	
	dcmpg("dcmpg", 1, "^dcmpg$", null, ""),
	dcmpl("dcmpl", 1, "^dcmpl$", null, ""),
	
	fcmpg("fcmpg", 1, "^fcmpg$", null, ""),
	fcmpl("fcmpl", 1, "^fcmpl$", null, ""),
	
	ireturn("ireturn", 1, "^ireturn$", null, ""),
	areturn("", 1, "^areturn$", null, "");
	
	/** enumeration of the types of an opcode */
	private enum OpcodeType { VALUE, OFFSET, CONSTANT_TABLE_INDEX, SWITCH };
	
	/** the name */
	public final String name;
	/** the offset to the following line */
	public final int followingLineOffset;
	/** the regular expression representing this opcode */
	public final String opcodeRegex;
	/** the type */
	private final OpcodeType type;
	/** the regular expression for this opcode */
	private final String typeRegex;
	
	/**
	 * Constructor for a new opcode.
	 * 
	 * @param name the new name
	 * @param followingLineOffset the new offset to the following line
	 * @param opcodeRegex the new regular expression representing this opcode
	 * @param type the new type
	 * @param typeRegex the new regular expression for this opcode
	 */
	Opcode(String name, int followingLineOffset, String opcodeRegex, OpcodeType type, String typeRegex) {
		this.name = name;
		this.followingLineOffset = followingLineOffset;
		this.opcodeRegex = opcodeRegex;
		this.type = type;
		this.typeRegex = typeRegex;
	}
	
	/**
	 * fromString returns the opcode thats representing regular expression
	 *  matches the given opcode name.
	 * 
	 * @param opcode the opcode name to get the matching opcode, thats
	 *  representing regular expression matches, for
	 * 
	 * @return the opcode thats representing regular expression matches the
	 *  given opcode name
	 */
	public static Opcode fromString(String opcode) {
		for(Opcode oc : values())
			if(opcode.matches(oc.opcodeRegex))
				return oc;
		Logger.getLogger(Opcode.class).fatal("no opcode matching \"" + opcode + "\"");
		throw new IllegalArgumentException("no opcode matching \"" + opcode + "\"");
	}
	
	/**
	 * getValueTypeGroup returns the '|'-separated list of the regular
	 *  expressions of the opcodes thats types are value.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are value
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
	 * getOffsetTypeGroup returns the '|'-separated list of the regular
	 *  expressions of the opcodes thats types are offset.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are offset
	 */
	public static String getOffsetTypeGroup() {
		StringBuilder offsetTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.OFFSET) {
				if(offsetTypeGroup.length() > 0)
					offsetTypeGroup.append("|");
				offsetTypeGroup.append(opcode.typeRegex);
			}
		}
		return offsetTypeGroup.toString();
	}
	
	/**
	 * getConstantTableIndexTypeGroup returns the '|'-separated list of the
	 *  regular expressions of the opcodes thats types are constant table
	 *  index.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are constant table index
	 */
	public static String getConstantTableIndexTypeGroup() {
		StringBuilder constantTableIndexTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.CONSTANT_TABLE_INDEX) {
				if(constantTableIndexTypeGroup.length() > 0)
					constantTableIndexTypeGroup.append("|");
				constantTableIndexTypeGroup.append(opcode.typeRegex);
			}
		}
		return constantTableIndexTypeGroup.toString();
	}
	
	/**
	 * getConstantSwitchGroup returns the '|'-separated list of the regular
	 *  expressions of the opcodes thats types are switch.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are switch
	 */
	public static String getConstantSwitchGroup() {
		StringBuilder constantSwitchGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.SWITCH) {
				if(constantSwitchGroup.length() > 0)
					constantSwitchGroup.append("|");
				constantSwitchGroup.append(opcode.typeRegex);
			}
		}
		return constantSwitchGroup.toString();
	}
}
