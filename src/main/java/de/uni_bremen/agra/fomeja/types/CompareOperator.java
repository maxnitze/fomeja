package de.uni_bremen.agra.fomeja.types;

/**
 * An enumeration of the six constraint operators EQUAL, GREATER EQUAL, GREATER
 * LESS EQUAL, LESS, and NOT EQUAL.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum CompareOperator {
	EQUAL("==", "!=", "==", "ifeq|if_Xcmpeq", "ifne|if_Xcmpne"),
	GREATER_EQUAL(">=", "<", "<=", "ifge|if_Xcmpge", "iflt|if_Xcmplt"),
	GREATER(">", "<=", "<", "ifgt|if_Xcmpgt", "ifle|if_Xcmple"),
	LESS_EQUAL("<=", ">", ">=", "ifle|if_Xcmple", "ifgt|if_Xcmpgt"),
	LESS("<", ">=", ">", "iflt|if_Xcmplt", "ifge|if_Xcmpge"),
	NOT_EQUAL("!=", "==", "!=", "ifne|if_Xcmpne", "ifeq|if_Xcmpeq");

	/** the ascii name */
	private final String asciiName;
	/** the opposite ascii name */
	private final String oppositeAsciiName;
	/** the swapped ascii name */
	private final String swappedAsciiName;
	/** the opcode regex */
	private final String opcode;
	/** the opposite opcode regex */
	private final String oppositeOpcode;

	/**
	 * Constructor for a new constraint operator.
	 * 
	 * @param asciiName the new ascii name
	 * @param oppositeAsciiName the new opposite ascii name
	 * @param swappedAsciiName the new swapped ascii name
	 * @param opcode the new opcode regex
	 * @param oppositeOpcode the new opposite opcode regex
	 */
	CompareOperator(String asciiName, String oppositeAsciiName, String swappedAsciiName, String opcode, String oppositeOpcode) {
		this.asciiName = asciiName;
		this.oppositeAsciiName = oppositeAsciiName;
		this.swappedAsciiName = swappedAsciiName;
		this.opcode = opcode;
		this.oppositeOpcode = oppositeOpcode;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getAsciiName() {
		return this.asciiName;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getOppositeAsciiName() {
		return this.oppositeAsciiName;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getSwappedAsciiName() {
		return this.swappedAsciiName;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getOpcode() {
		return this.opcode;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getOppositeOpcode() {
		return this.oppositeOpcode;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public CompareOperator getOpposite() {
		for (CompareOperator co : values())
			if (this.oppositeAsciiName.equals(co.asciiName))
				return co;
		throw new IllegalArgumentException("no constant with opposite ascii name \"" + asciiName + "\" found");
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public CompareOperator getSwapped() {
		for (CompareOperator co : values())
			if (this.swappedAsciiName.equals(co.asciiName))
				return co;
		throw new IllegalArgumentException("no constant with swapped ascii name \"" + asciiName + "\" found");
	}

	/**
	 * fromAsciiName returns the constraint operator with the given ascii name.
	 * 
	 * @param asciiName the ascii name to look for
	 * 
	 * @return the constraint operator with the given ascii name
	 */
	public static CompareOperator fromAsciiName(String asciiName) {
		for (CompareOperator co : values())
			if (asciiName.equals(co.asciiName))
				return co;
		throw new IllegalArgumentException("no constant with ascii name \"" + asciiName + "\" found");
	}

	/**
	 * fromOppositeAsciiName returns the constraint operator with the given
	 *  opposite ascii name.
	 * 
	 * @param oppositeAsciiName the opposite ascii name to look for
	 * 
	 * @return the constraint operator with the given opposite ascii name
	 */
	public static CompareOperator fromOppositeAsciiName(String oppositeAsciiName) {
		for (CompareOperator co : values())
			if (oppositeAsciiName.equals(co.oppositeAsciiName))
				return co;
		throw new IllegalArgumentException("no constant with opposite ascii name \"" + oppositeAsciiName + "\" found");
	}

	/**
	 * fromSwappedAsciiName returns the constraint operator with the given
	 *  swapped ascii name.
	 * 
	 * @param swappedAsciiName the swapped ascii name to look for
	 * 
	 * @return the constraint operator with the given swapped ascii name
	 */
	public static CompareOperator fromSwappedAsciiName(String swappedAsciiName) {
		for (CompareOperator co : values())
			if (swappedAsciiName.equals(co.swappedAsciiName))
				return co;
		throw new IllegalArgumentException("no constant with swapped ascii name \"" + swappedAsciiName + "\" found");
	}

	/**
	 * fromOpcode returns the constraint operator with the given opcode.
	 * 
	 * @param opcode the opcode to look for
	 * 
	 * @return the constraint operator with the given opcode
	 */
	public static CompareOperator fromOpcode(String opcode) {
		for (CompareOperator co : values())
			if (opcode.matches(co.opcode))
				return co;
		throw new IllegalArgumentException("no constant with opcode \"" + opcode + "\" found");
	}

	/**
	 * fromOpcode returns the constraint operator with the given opposite
	 *  opcode.
	 * 
	 * @param oppositeOpcode the opposite opcode to look for
	 * 
	 * @return the constraint operator with the given opposite opcode
	 */
	public static CompareOperator fromOppositeOpcode(String oppositeOpcode) {
		for (CompareOperator co : values())
			if (oppositeOpcode.matches(co.oppositeOpcode))
				return co;
		throw new IllegalArgumentException("no constant with opposite opcode \"" + oppositeOpcode + "\" found");
	}

	/**
	 * compare compares the two given numbers by this constraint operator.
	 * 
	 * @param number1 the first number to compare
	 * @param number2 the second number to compare
	 * 
	 * @return {@code true} if the comparison of the two given numbers
	 *  evaluates to {@code true} applying this constraint operator, {@code
	 *  false} otherwise
	 * 
	 * @param <T> COMMENT
	 */
	public <T extends Comparable<T>> boolean compare(T number1, T number2) {
		switch(this) {
		case EQUAL:
			return number1.compareTo(number2) == 0;
		case GREATER:
			return number1.compareTo(number2) > 0;
		case GREATER_EQUAL:
			return number1.compareTo(number2) >= 0;
		case LESS:
			return number1.compareTo(number2) < 0;
		case LESS_EQUAL:
			return number1.compareTo(number2) <= 0;
		case NOT_EQUAL:
			return number1.compareTo(number2) != 0;
		default:
			return false;
		}
	}
}
