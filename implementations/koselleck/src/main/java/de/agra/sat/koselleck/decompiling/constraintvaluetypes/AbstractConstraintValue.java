package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.datatypes.PreFieldList;
import de.agra.sat.koselleck.types.Opcode;

/**
 * AbstractConstraint is an abstract class for all types of constraint values.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AbstractConstraintValue {
	/** COMMENT */
	private PreFieldList preFieldList;

	/**
	 * COMMENT
	 */
	public AbstractConstraintValue() {
		this.preFieldList = new PreFieldList(-1, null);
	}

	/**
	 * COMMENT
	 * 
	 * @param fieldCodeIndex
	 * @param opcode
	 */
	public AbstractConstraintValue(int fieldCodeIndex, Opcode opcode) {
		this.preFieldList = new PreFieldList(fieldCodeIndex, opcode);
	}

	/**
	 * COMMENT
	 * 
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param preFields
	 */
	public AbstractConstraintValue(int fieldCodeIndex, Opcode opcode, List<PreField> preFields) {
		this.preFieldList = new PreFieldList(fieldCodeIndex, opcode, preFields);
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreFieldList getPreFieldList() {
		return this.preFieldList;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getFieldCodeIndex() {
		return this.preFieldList.getFieldCodeIndex();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Opcode getOpcode() {
		return this.preFieldList.getOpcode();
	}

	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * replaceAll replaces all occurrences of the given regular expression
	 * 	{@code regex} with the given {@code replacement}.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the replacement
	 */
	public abstract void replaceAll(String regex, String replacement);

	/**
	 * evaluate evaluates the abstract constraint value.
	 * 
	 * @return the new evaluated or this abstract constraint value 
	 */
	public abstract AbstractConstraintValue evaluate();

	/**
	 * substitute substitutes the abstract constraint value with the given
	 *  objects (method parameters).
	 * 
	 * @param constraintArguments the arguments the substitute the constraint
	 *  values with
	 */
	public abstract AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments);

	/**
	 * matches checks if this abstract constraint value matches the given
	 *  regular expression {@code regex}.
	 * 
	 * @param regex the regular expression
	 * 
	 * @return {@code true} if this abstract constraint value matches the given
	 *  regular expression {@code regex}, {@code false} otherwise
	 */
	public abstract boolean matches(String regex);

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals();

	/**
	 * equals checks if this abstract constraint value and the given object are
	 *  equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object matches this abstract
	 *  constraint value, {@code false} otherwise
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * clone returns a copy of this abstract constraint value.
	 * 
	 * @return a copy of this abstract constraint value
	 */
	@Override
	public abstract AbstractConstraintValue clone();

	/**
	 * toString returns the string representation of this abstract constraint
	 *  value.
	 * 
	 * @return the string representation of this abstract constraint value
	 */
	@Override
	public abstract String toString();
}
