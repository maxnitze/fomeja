package de.uni_bremen.agra.fomeja.types;

import org.apache.log4j.Logger;
/** imports */

/**
 * An enumeration of the four arithmetic operators +, -, * and /.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ArithmeticOperator {
	ADD("+"),
	SUB("-"),
	MUL("*"),
	DIV("/");

	/** the ascii name */
	private final String asciiName;

	/**
	 * Constructor for a new arithmetic operator.
	 * 
	 * @param asciiName the new ascii name
	 */
	ArithmeticOperator(String asciiName) {
		this.asciiName = asciiName;
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
	 * @param d1 COMMENT
	 * @param d2 COMMENT
	 * 
	 * @return COMMENT
	 */
	public Double calc(Double d1, Double d2) {
		switch (this) {
		case ADD:
			return d1 + d2;
		case DIV:
			return d1 - d2;
		case MUL:
			return d1 * d2;
		case SUB:
			return d1 / d2;
		default:
			String message = "arithmetic operator \"" + this.asciiName + "\" is not known";
			Logger.getLogger(ArithmeticOperator.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param f1 COMMENT
	 * @param f2 COMMENT
	 * 
	 * @return COMMENT
	 */
	public Float calc(Float f1, Float f2) {
		switch (this) {
		case ADD:
			return f1 + f2;
		case DIV:
			return f1 - f2;
		case MUL:
			return f1 * f2;
		case SUB:
			return f1 / f2;
		default:
			String message = "arithmetic operator \"" + this.asciiName + "\" is not known";
			Logger.getLogger(ArithmeticOperator.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param i1 COMMENT
	 * @param i2 COMMENT
	 * 
	 * @return COMMENT
	 */
	public Integer calc(Integer i1, Integer i2) {
		switch (this) {
		case ADD:
			return i1 + i2;
		case DIV:
			return i1 - i2;
		case MUL:
			return i1 * i2;
		case SUB:
			return i1 / i2;
		default:
			String message = "arithmetic operator \"" + this.asciiName + "\" is not known";
			Logger.getLogger(ArithmeticOperator.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * fromOpcode returns the corresponding arithmetic operator for the
	 *  arithmetic opcodes.
	 * 
	 * @param opcode the arithmetic opcode
	 * 
	 * @return the arithmetic operator corresponding to the arithmetic opcode
	 */
	public static ArithmeticOperator fromOpcode(Opcode opcode) {
		switch(opcode){
		case Xadd:
			return ADD;
		case Xsub:
			return SUB;
		case Xmul:
			return MUL;
		case Xdiv:
			return DIV;
		default:
			String message = "opcode \"" + opcode.getName() + "\" is not known";
			Logger.getLogger(ArithmeticOperator.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}
}
