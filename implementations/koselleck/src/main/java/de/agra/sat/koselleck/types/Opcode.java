package de.agra.sat.koselleck.types;

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
	Xload_("Xload_", 1, OpcodeType.SIMPLE_VALUE, "[i|f|d|a]load_"),
	Xload("Xload", 2, OpcodeType.SIMPLE_VALUE, "[i|f|d|a]load( )?"),
	Xstore_("Xstore_", 1, OpcodeType.SIMPLE_VALUE, "[i|f|d|a]store_"),
	Xstore("Xstore", 2, OpcodeType.SIMPLE_VALUE, "[i|f|d|a]store( )?"),

	Xconst_("bconst_", 1, OpcodeType.SIMPLE_VALUE, "[i|f|b]const_"),
	Xconst("bconst", 2, OpcodeType.SIMPLE_VALUE, "[i|f|b]const( )?"),
	bipush("bipush", 2, OpcodeType.SIMPLE_VALUE, "bipush "),
	
	getfield("getfield", 3, OpcodeType.CONSTANT_TABLE_INDEX, "getfield"),
	getstatic("getstatic", 3, OpcodeType.CONSTANT_TABLE_INDEX, "getstatic"),
	
	checkcast("checkcast", 3, OpcodeType.CONSTANT_TABLE_INDEX, "checkcast"),
	
	i2d("i2d", 1, OpcodeType.SIMPLE, "i2d"),
	i2f("i2f", 1, OpcodeType.SIMPLE, "i2f"),
	f2d("f2d", 1, OpcodeType.SIMPLE, "f2d"),
	
	ldc("ldc", 2, OpcodeType.CONSTANT_TABLE_VALUE, "ldc"),
	ldc2_w("ldc2_w", 3, OpcodeType.CONSTANT_TABLE_VALUE, "ldc2_w"),
	
	Xadd("Xadd", 1, OpcodeType.SIMPLE, "[i|f|d]add"),
	Xsub("Xsub", 1, OpcodeType.SIMPLE, "[i|f|d]sub"),
	Xmul("Xmul", 1, OpcodeType.SIMPLE, "[i|f|d]mul"),
	Xdiv("Xdiv", 1, OpcodeType.SIMPLE, "[i|f|d]div"),
	
	_new("new", 3, OpcodeType.CONSTANT_TABLE_INDEX, "new"),
	
	invokestatic("invokestatic", 3, OpcodeType.CONSTANT_TABLE_INDEX, "invokestatic"),
	invokevirtual("invokevirtual", 3, OpcodeType.CONSTANT_TABLE_INDEX, "invokevirtual"),
	invokespecial("invokespecial", 3, OpcodeType.CONSTANT_TABLE_INDEX, "invokespecial"),
	
	dup("dup", 1, OpcodeType.SIMPLE, "dup"),
	
	tableswitch("tableswitch", 0, OpcodeType.SWITCH, "tableswitch"),
	
	_goto("goto", 1, OpcodeType.OFFSET, "goto"),
	
	ifeq("ifeq", 3, OpcodeType.OFFSET, "ifeq"),							/** jump if zero */
	ifne("ifne", 3, OpcodeType.OFFSET, "ifne"),							/** jump if nonzero */
	
	if_Xcmpeq("if_Xcmpeq", 3, OpcodeType.OFFSET, "if_[i|a]cmpeq"),		/** equal */
	if_Xcmpge("if_Xcmpge", 3, OpcodeType.OFFSET, "if_[i|a]cmpge"),		/** greater-equal */
	if_Xcmpgt("if_Xcmpgt", 3, OpcodeType.OFFSET, "if_[i|a]cmpgt"),		/** greater */
	if_Xcmple("if_Xcmple", 3, OpcodeType.OFFSET, "if_[i|a]cmple"),		/** less-equal */
	if_Xcmplt("if_Xcmplt", 3, OpcodeType.OFFSET, "if_[i|a]cmplt"),		/** less */
	if_Xcmpne("if_Xcmpne", 3, OpcodeType.OFFSET, "if_[i|a]cmpne"),		/** not equal */
	
	dcmpg("dcmpg", 1, OpcodeType.SIMPLE, "dcmpg"),
	dcmpl("dcmpl", 1, OpcodeType.SIMPLE, "dcmpl"),
	
	fcmpg("fcmpg", 1, OpcodeType.SIMPLE, "fcmpg"),
	fcmpl("fcmpl", 1, OpcodeType.SIMPLE, "fcmpl"),
	
	_return("return", 1, OpcodeType.SIMPLE, "[i|f|d|a]return");
	
	/** enumeration of the types of an opcode */
	private enum OpcodeType { SIMPLE, SIMPLE_VALUE, CONSTANT_TABLE_VALUE, OFFSET, CONSTANT_TABLE_INDEX, SWITCH };
	
	/** the name */
	public final String name;
	/** the offset to the following line */
	public final int followingLineOffset;
	/** the type */
	private final OpcodeType type;
	/** the regular expression for this opcode */
	private final String opcodeRegex;
	
	/**
	 * Constructor for a new opcode.
	 * 
	 * @param name the new name
	 * @param followingLineOffset the new offset to the following line
	 * @param type the new type
	 * @param opcodeRegex the new regular expression for this opcode
	 */
	Opcode(String name, int followingLineOffset, OpcodeType type, String opcodeRegex) {
		this.name = name;
		this.followingLineOffset = followingLineOffset;
		this.type = type;
		this.opcodeRegex = opcodeRegex;
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
			if(opcode.matches("^" + oc.opcodeRegex + "$"))
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
				simpleTypeGroup.append(opcode.opcodeRegex);
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
				simpleValueTypeGroup.append(opcode.opcodeRegex);
			}
		}
		return simpleValueTypeGroup.toString();
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
				valueTypeGroup.append(opcode.opcodeRegex);
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
				offsetTypeGroup.append(opcode.opcodeRegex);
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
				constantTableIndexTypeGroup.append(opcode.opcodeRegex);
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
				constantSwitchGroup.append(opcode.opcodeRegex);
			}
		}
		return constantSwitchGroup.toString();
	}
}
