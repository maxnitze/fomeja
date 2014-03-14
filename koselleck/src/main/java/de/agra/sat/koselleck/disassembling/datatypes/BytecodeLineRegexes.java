package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * BytecodeLineRegexes provides regular expressions to identify the different
 *  byte code lines of a disassembled method.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class BytecodeLineRegexes {
	/** regular expression for the line number of a byte code line */
	public static final String lineNumber = "^(?<lineNumber>\\d+): .*$";
	/** regular expression for the opcode of a byte code line */
	public static final String opcode = "^\\d+: (?<opcode>\\S+).*$";
	/** regular expression for switch-case byte code lines  */
	public static final String switchCase = "^(?<case>(default|\\d+)): (?<offset>\\d+)$";
	
	/** regular expression for value typed opcodes of a byte code line */
	public static final String value = "^\\d+: (" + Opcode.getValueTypeGroup() + ")(?<value>\\d+)$";
	/** regular expression for offset typed opcodes of a byte code line */
	public static final String offset = "^\\d+: (" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$";
	/** regular expression for constant table index typed opcodes of a byte
	 * code line */
	public static final String constantTableIndex = "^\\d+: (" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) .*$";
	/** regular expression for tableswitch typed opcodes of a byte code line */
	public static final String tableswitch = "^\\d+: (" + Opcode.getConstantSwitchGroup() + ")\\s+\\{\\s// \\d+ to \\d+$";

	/** regular expression for a valued byte code line */
	public static final String typeRegex = "^\\d+: \\S+ #?\\d+ // (?<type>\\S+) (?<qfield>\\S+)$";
	/** regular expression for a valued byte code line */
	public static final String typeMethodFieldRegex = "^\\d+: \\S+ #?\\d+ // (?<type>\\S+) (?<qfield>\\S+):(\\((?<paramtypes>\\S+)\\))?(?<rtype>\\S+)$";
}
