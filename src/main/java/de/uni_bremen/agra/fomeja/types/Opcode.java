package de.uni_bremen.agra.fomeja.types;

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
	Xload_("Xload_", 1, OpcodeType.SIMPLE_VALUE, "[ifda]load_"),
	Xload("Xload", 2, OpcodeType.SIMPLE_VALUE, "[ifda]load"),
	Xstore_("Xstore_", 1, OpcodeType.SIMPLE_VALUE, "[ifda]store_"),
	Xstore("Xstore", 2, OpcodeType.SIMPLE_VALUE, "[ifda]store"),

	iinc("iinc", 3, OpcodeType.MULTIPLE_VALUE, "iinc"),

	Xconst_("Xconst_", 1, OpcodeType.SIMPLE_VALUE, "[ifd]const_"),
	Xconst("Xconst", 2, OpcodeType.SIMPLE_VALUE, "[ifd]const"),
	bipush("bipush", 2, OpcodeType.SIMPLE_VALUE, "bipush"),
	sipush("bipush", 3, OpcodeType.SIMPLE_VALUE, "sipush"),

	getfield("getfield", 3, OpcodeType.CONSTANT_TABLE_INDEX, "getfield"),
	getstatic("getstatic", 3, OpcodeType.CONSTANT_TABLE_INDEX, "getstatic"),

	checkcast("checkcast", 3, OpcodeType.CONSTANT_TABLE_INDEX, "checkcast"),

	i2d("i2d", 1, OpcodeType.SIMPLE, "i2d"),
	i2f("i2f", 1, OpcodeType.SIMPLE, "i2f"),
	f2d("f2d", 1, OpcodeType.SIMPLE, "f2d"),

	irem("irem", 1, OpcodeType.SIMPLE, "irem"),
	frem("frem", 1, OpcodeType.SIMPLE, "frem"),
	drem("drem", 1, OpcodeType.SIMPLE, "drem"),
	lrem("lrem", 1, OpcodeType.SIMPLE, "lrem"),

	ldc("ldc", 2, OpcodeType.CONSTANT_TABLE_VALUE, "ldc"),
	ldc2_w("ldc2_w", 3, OpcodeType.CONSTANT_TABLE_VALUE, "ldc2_w"),

	Xadd("Xadd", 1, OpcodeType.SIMPLE, "[ifd]add"),
	Xsub("Xsub", 1, OpcodeType.SIMPLE, "[ifd]sub"),
	Xmul("Xmul", 1, OpcodeType.SIMPLE, "[ifd]mul"),
	Xdiv("Xdiv", 1, OpcodeType.SIMPLE, "[ifd]div"),

	_new("new", 3, OpcodeType.CONSTANT_TABLE_INDEX, "new"),

	invokestatic("invokestatic", 3, OpcodeType.CONSTANT_TABLE_INDEX, "invokestatic"),
	invokevirtual("invokevirtual", 3, OpcodeType.CONSTANT_TABLE_INDEX, "invokevirtual"),
	invokespecial("invokespecial", 3, OpcodeType.CONSTANT_TABLE_INDEX, "invokespecial"),

	dup("dup", 1, OpcodeType.SIMPLE, "dup"),

	newarray("newarray", 2, OpcodeType.SIMPLE_VALUE, "newarray"),
	anewarray("anewarray", 3, OpcodeType.CONSTANT_TABLE_INDEX, "anewarray"),
	arraylength("arraylength", 1, OpcodeType.SIMPLE, "arraylength"),
	Xaload("Xaload", 1, OpcodeType.SIMPLE, "[cifda]aload"),
	Xastore("Xastore", 1, OpcodeType.SIMPLE, "[cifda]astore"),

	tableswitch("tableswitch", 0, OpcodeType.SWITCH, "tableswitch"),

	_goto("goto", 1, OpcodeType.OFFSET, "goto"),

	ifnull("ifnull", 3, OpcodeType.OFFSET, "ifnull"),

	ifeq("ifeq", 3, OpcodeType.OFFSET, "ifeq"),							/** jump if equals to zero */
	ifge("ifge", 3, OpcodeType.OFFSET, "ifge"),							/** jump if greater-equal zero */
	ifgt("ifgt", 3, OpcodeType.OFFSET, "ifgt"),							/** jump if greater than zero */
	ifle("ifle", 3, OpcodeType.OFFSET, "ifle"),							/** jump if lower equal zero */
	iflt("iflt", 3, OpcodeType.OFFSET, "iflt"),							/** jump if lower than zero */
	ifne("ifne", 3, OpcodeType.OFFSET, "ifne"),							/** jump if non-equal to zero */

	if_Xcmpeq("if_Xcmpeq", 3, OpcodeType.OFFSET, "if_[ia]cmpeq"),		/** equal */
	if_Xcmpge("if_Xcmpge", 3, OpcodeType.OFFSET, "if_[ia]cmpge"),		/** greater-equal */
	if_Xcmpgt("if_Xcmpgt", 3, OpcodeType.OFFSET, "if_[ia]cmpgt"),		/** greater */
	if_Xcmple("if_Xcmple", 3, OpcodeType.OFFSET, "if_[ia]cmple"),		/** less-equal */
	if_Xcmplt("if_Xcmplt", 3, OpcodeType.OFFSET, "if_[ia]cmplt"),		/** less */
	if_Xcmpne("if_Xcmpne", 3, OpcodeType.OFFSET, "if_[ia]cmpne"),		/** not equal */

	dcmpg("dcmpg", 1, OpcodeType.SIMPLE, "dcmpg"),
	dcmpl("dcmpl", 1, OpcodeType.SIMPLE, "dcmpl"),

	fcmpg("fcmpg", 1, OpcodeType.SIMPLE, "fcmpg"),
	fcmpl("fcmpl", 1, OpcodeType.SIMPLE, "fcmpl"),

	_return("return", 1, OpcodeType.SIMPLE, "[ifda]return");

	/** regexp group of simple typed opcodes */
	public static final String simpleTypeGroup = getGroupForType(OpcodeType.SIMPLE);
	/** regexp group of simple typed opcodes */
	public static final String simpleValueTypeGroup = getGroupForType(OpcodeType.SIMPLE_VALUE);
	/** regexp group of simple typed opcodes */
	public static final String multipleValueTypeGroup = getGroupForType(OpcodeType.MULTIPLE_VALUE);
	/** regexp group of simple typed opcodes */
	public static final String constantTableValueTypeGroup = getGroupForType(OpcodeType.CONSTANT_TABLE_VALUE);
	/** regexp group of simple typed opcodes */
	public static final String offsetTypeGroup = getGroupForType(OpcodeType.OFFSET);
	/** regexp group of simple typed opcodes */
	public static final String constantTableIndexTypeGroup = getGroupForType(OpcodeType.CONSTANT_TABLE_INDEX);
	/** regexp group of simple typed opcodes */
	public static final String switchTypeGroup = getGroupForType(OpcodeType.SWITCH);

	/** enumeration of the types of an opcode */
	private enum OpcodeType { SIMPLE, SIMPLE_VALUE, MULTIPLE_VALUE, CONSTANT_TABLE_VALUE, OFFSET, CONSTANT_TABLE_INDEX, SWITCH };

	/** the name */
	private final String name;
	/** the offset to the following line */
	private final int followingLineOffset;
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

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getFollowingLineOffset() {
		return this.followingLineOffset;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

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
		for (Opcode oc : values())
			if (opcode.matches("^" + oc.opcodeRegex + "$"))
				return oc;
		String message = "no opcode matching \"" + opcode + "\"";
		Logger.getLogger(Opcode.class).fatal(message);
		throw new IllegalArgumentException(message);
	}

	/**
	 * getGroupForType returns the '|'-separated list of the regular
	 *  expressions of the opcodes with the given type.
	 * 
	 * @param type the type of the opcodes to create the group for
	 * 
	 * @return the '|'-separated list of the regular expressions of the opcodes
	 *  with the given type
	 */
	private static String getGroupForType(OpcodeType type) {
		StringBuilder simpleTypeGroup = new StringBuilder();
		for (Opcode opcode : values()) {
			if (opcode.type == type) {
				if (simpleTypeGroup.length() > 0)
					simpleTypeGroup.append("|");
				simpleTypeGroup.append(opcode.opcodeRegex);
			}
		}
		return simpleTypeGroup.toString();
	}
}
