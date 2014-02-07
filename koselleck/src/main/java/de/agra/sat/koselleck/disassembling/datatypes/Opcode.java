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
	load_("load_", 1, "^[i|f|d|a]load_\\d+$", OpcodeType.SIMPLE_VALUE, "[i|f|d|a]load"),
	load("load", 2, "^[i|f|d|a]load$", OpcodeType.VALUE, "[i|f|d|a]load"),
	store_("store_", 1, "^[i|f|d|a]store_\\d+$", OpcodeType.SIMPLE_VALUE, "[i|f|d|a]store"),
	store("store", 2, "^[i|f|d|a]store$", OpcodeType.VALUE, "[i|f|d|a]store"),

	bconst_("bconst_", 1, "^[i|f|b]const_\\d+$", OpcodeType.SIMPLE_VALUE, "[i|f|b]const_"),
	bconst("bconst", 2, "^[i|f|b]const$", OpcodeType.VALUE, "[i|f|b]const"),
	bipush("bipush", 2, "^bipush$", OpcodeType.VALUE, "bipush"),
	
	getfield("getfield", 3, "^getfield$", OpcodeType.CONSTANT_TABLE_INDEX, "getfield"),
	getstatic("getstatic", 3, "^getstatic$", OpcodeType.CONSTANT_TABLE_INDEX, "getstatic"),
	
	checkcast("checkcast", 3, "^checkcast$", OpcodeType.CONSTANT_TABLE_INDEX, "checkcast"),
	
	i2d("i2d", 1, "^i2d$", OpcodeType.SIMPLE, "i2d"),
	i2f("i2f", 1, "^i2f$", OpcodeType.SIMPLE, "i2f"),
	f2d("f2d", 1, "^f2d$", OpcodeType.SIMPLE, "f2d"),
	
	ldc("ldc", 2, "^ldc", OpcodeType.CONSTANT_TABLE_VALUE, "ldc"),
	ldc2_w("ldc2_w", 3, "^ldc2_w$", OpcodeType.CONSTANT_TABLE_VALUE, "ldc2_w"),
	
	add("add", 1, "^[i|f|d]add$", OpcodeType.SIMPLE, "[i|f|d]add"),
	sub("sub", 1, "^[i|f|d]sub$", OpcodeType.SIMPLE, "[i|f|d]sub"),
	mul("mul", 1, "^[i|f|d]mul$", OpcodeType.SIMPLE, "[i|f|d]mul"),
	div("div", 1, "^[i|f|d]div$", OpcodeType.SIMPLE, "[i|f|d]div"),
	
	_new("new", 3, "^new$", OpcodeType.CONSTANT_TABLE_INDEX, "new"),
	
	invokestatic("invokestatic", 3, "^invokestatic$", OpcodeType.CONSTANT_TABLE_INDEX, "invokestatic"),
	invokevirtual("invokevirtual", 3, "^invokevirtual$", OpcodeType.CONSTANT_TABLE_INDEX, "invokevirtual"),
	invokespecial("invokespecial", 3, "^invokespecial$", OpcodeType.CONSTANT_TABLE_INDEX, "invokespecial"),
	
	dup("dup", 1, "^dup$", OpcodeType.SIMPLE, "dup"),
	
	tableswitch("tableswitch", 0, "^tableswitch$", OpcodeType.SWITCH, "tableswitch"),
	
	_goto("goto", 1, "^goto$", OpcodeType.OFFSET, "goto"),
	
	ifeq("ifeq", 3, "^ifeq$", OpcodeType.OFFSET, "ifeq"),							/** jump if zero */
	ifne("ifne", 3, "^ifne$", OpcodeType.OFFSET, "ifne"),							/** jump if nonzero */
	
	if_icmpeq("if_icmpeq", 3, "^if_icmpeq$", OpcodeType.OFFSET, "if_icmpeq"),		/** equal */
	if_icmpge("if_icmpge", 3, "^if_icmpge$", OpcodeType.OFFSET, "if_icmpge"),		/** greater-equal */
	if_icmpgt("if_icmpgt", 3, "^if_icmpgt$", OpcodeType.OFFSET, "if_icmpgt"),		/** greater */
	if_icmple("if_icmple", 3, "^if_icmple$", OpcodeType.OFFSET, "if_icmple"),		/** less-equal */
	if_icmplt("if_icmplt", 3, "^if_icmplt$", OpcodeType.OFFSET, "if_icmplt"),		/** less */
	if_icmpne("if_icmpne", 3, "^if_icmpne$", OpcodeType.OFFSET, "if_icmpne"),		/** not equal */
	
	dcmpg("dcmpg", 1, "^dcmpg$", OpcodeType.SIMPLE, "dcmpg"),
	dcmpl("dcmpl", 1, "^dcmpl$", OpcodeType.SIMPLE, "dcmpg"),
	
	fcmpg("fcmpg", 1, "^fcmpg$", OpcodeType.SIMPLE, "fcmpg"),
	fcmpl("fcmpl", 1, "^fcmpl$", OpcodeType.SIMPLE, "fcmpg"),
	
	_return("return", 1, "^[i|f|d|a]return$", OpcodeType.SIMPLE, "[i|f|d|a]return");
	
	/** enumeration of the types of an opcode */
	private enum OpcodeType { SIMPLE, SIMPLE_VALUE, VALUE, CONSTANT_TABLE_VALUE, OFFSET, CONSTANT_TABLE_INDEX, SWITCH };
	
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
	 * getSimpleTypeGroup returns the '|'-separated list of the regular
	 *  expressions of the opcodes thats types are simple.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are simple
	 */
	public static String getSimpleTypeGroup() {
		StringBuilder simpleTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.SIMPLE) {
				if(simpleTypeGroup.length() > 0)
					simpleTypeGroup.append("|");
				simpleTypeGroup.append(opcode.typeRegex);
			}
		}
		return simpleTypeGroup.toString();
	}
	
	/**
	 * getSimpleValueTypeGroup returns the '|'-separated list of the regular
	 *  expressions of the opcodes thats types are simple value.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are simple value
	 */
	public static String getSimpleValueTypeGroup() {
		StringBuilder simpleValueTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.SIMPLE_VALUE) {
				if(simpleValueTypeGroup.length() > 0)
					simpleValueTypeGroup.append("|");
				simpleValueTypeGroup.append(opcode.typeRegex);
			}
		}
		return simpleValueTypeGroup.toString();
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
	 * getConstantTableValueTypeGroup returns the '|'-separated list of the
	 *  regular expressions of the opcodes thats types are constant table
	 *  value.
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  thats types are constant table value
	 */
	public static String getConstantTableValueTypeGroup() {
		StringBuilder valueTypeGroup = new StringBuilder("");
		for(Opcode opcode : values()) {
			if(opcode.type == OpcodeType.CONSTANT_TABLE_VALUE) {
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
