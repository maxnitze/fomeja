package de.agra.sat.koselleck.types;

/**
 * An enumeration of the six constraint operators ==, >=, >, <=, < and !=.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ConstraintOperator {
	EQUAL("==", "!=", "==", "if_Xcmpeq", "if_Xcmpne"),
	GREATER_EQUAL(">=", "<", "<=", "if_Xcmpge", "if_Xcmplt"),
	GREATER(">", "<=", "<", "if_Xcmpgt", "if_Xcmple"),
	LESS_EQUAL("<=", ">", ">=", "if_Xcmple", "if_Xcmpgt"),
	LESS("<", ">=", ">", "if_Xcmplt", "if_Xcmpge"),
	NOT_EQUAL("!=", "==", "!=", "if_Xcmpne", "if_Xcmpeq");

	/** the ascii name */
	public final String asciiName;
	/** the opposite ascii name */
	public final String oppositeAsciiName;
	/** the swapped ascii name */
	public final String swappedAsciiName;
	/** the opcode regex */
	public final String opcode;
	/** the opposite opcode regex */
	public final String oppositeOpcode;

	/**
	 * Constructor for a new constraint operator.
	 * 
	 * @param asciiName the new ascii name
	 * @param oppositeAsciiName the new opposite ascii name
	 * @param swappedAsciiName the new swapped ascii name
	 * @param opcode the new opcode regex
	 * @param oppositeOpcode the new opposite opcode regex
	 */
	ConstraintOperator(String asciiName, String oppositeAsciiName, String swappedAsciiName, String opcode, String oppositeOpcode) {
		this.asciiName = asciiName;
		this.oppositeAsciiName = oppositeAsciiName;
		this.swappedAsciiName = swappedAsciiName;
		this.opcode = opcode;
		this.oppositeOpcode = oppositeOpcode;
	}

	public ConstraintOperator getOpposite() {
		for(ConstraintOperator co : values())
			if(this.oppositeAsciiName.equals(co.asciiName))
				return co;
		throw new IllegalArgumentException("no constant with ascii name \"" + asciiName + "\" found");
	}

	/**
	 * fromAsciiName returns the constraint operator with the given ascii name.
	 * 
	 * @param asciiName the ascii name to look for
	 * 
	 * @return the constraint operator with the given ascii name
	 */
	public static ConstraintOperator fromAsciiName(String asciiName) {
		for(ConstraintOperator co : values())
			if(asciiName.equals(co.asciiName))
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
	public static ConstraintOperator fromOppositeAsciiName(String oppositeAsciiName) {
		for(ConstraintOperator co : values())
			if(oppositeAsciiName.equals(co.oppositeAsciiName))
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
	public static ConstraintOperator fromSwappedAsciiName(String swappedAsciiName) {
		for(ConstraintOperator co : values())
			if(swappedAsciiName.equals(co.swappedAsciiName))
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
	public static ConstraintOperator fromOpcode(String opcode) {
		for(ConstraintOperator co : values())
			if(opcode.matches(co.opcode))
				return co;
		throw new IllegalArgumentException("no constant with opcode \"" + opcode + "\" found");
	}

	/**
	 * fromOpcode returns the constraint operator with the given opposite
	 *  opcode.
	 * 
	 * @param opcode the opposite opcode to look for
	 * 
	 * @return the constraint operator with the given opposite opcode
	 */
	public static ConstraintOperator fromOppositeOpcode(String oppositeOpcode) {
		for(ConstraintOperator co : values())
			if(oppositeOpcode.matches(co.oppositeOpcode))
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
