package de.agra.sat.koselleck.disassembling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public abstract class BytecodeLineRegexes {
	/**  */
	public static final String lineNumber = "^(?<lineNumber>\\d+): .*$";
	/**  */
	public static final String opcode = "^\\d+: (?<opcode>\\S+).*$";
	/**  */
	public static final String switchCase = "^(?<case>(default|\\d+)): (?<offset>\\d+)$";
	
	/**  */
	public static final String value = "^\\d+: (" + Opcode.getValueTypeGroup() + ")(?<value>\\d+)$";
	/**  */
	public static final String offset = "^\\d+: (" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$";
	/**  */
	public static final String constantTableIndex = "^\\d+: (" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) .*$";
	/**  */
	public static final String tableswitch = "^\\d+: (" + Opcode.getConstantSwitchGroup() + ")\\s+\\{\\s// \\d+ to \\d+$";
}
