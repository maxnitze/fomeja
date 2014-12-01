package de.agra.sat.koselleck.decompiling.constrainttypes;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;

/** imports */

/**
 * AbstractBooleanConstraint represents a boolean value in a constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractBooleanConstraint extends AbstractConstraint {
	/** the boolean value */
	private final boolean value;
	/** the return value of the method evaluated to {@code value} */
	private AbstractConstraintValue returnValue;

	/**
	 * Constructor for a new AbstractBooleanConstraint.
	 * 
	 * @param value the new boolean value
	 */
	public AbstractBooleanConstraint(boolean value) {
		this.value = value;
		this.returnValue = new AbstractConstraintLiteralInteger(value ? 1 : 0);
	}

	/**
	 * Constructor for a new AbstractBooleanConstraint.
	 * 
	 * @param value the new boolean value
	 * @param returnValue the new return value of the method evaluated to {@code
	 *  value}
	 */
	public AbstractBooleanConstraint(boolean value, AbstractConstraintValue returnValue) {
		this.value = value;
		this.returnValue = returnValue;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public boolean getValue() {
		return this.value;
	}

	/**
	 * 
	 * @return
	 */
	public AbstractConstraintValue getReturnValue() {
		return this.returnValue;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.returnValue.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraint evaluate() {
		this.returnValue = this.returnValue.evaluate();

		return this;
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {}

	@Override
	public boolean matches(String regex) {
		return this.returnValue.matches(regex);
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiterals = new HashSet<AbstractConstraintLiteral<?>>();
		unfinishedConstraintLiterals.addAll(this.returnValue.getUnfinishedConstraintLiterals());

		return unfinishedConstraintLiterals;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractBooleanConstraint))
			return false;

		AbstractBooleanConstraint booleanConstraint = (AbstractBooleanConstraint)object;

		return this.value == booleanConstraint.value &&
				this.returnValue.equals(booleanConstraint.returnValue);
	}

	@Override
	public AbstractBooleanConstraint clone() {
		return new AbstractBooleanConstraint(this.value, this.returnValue);
	}

	@Override
	public String toString() {
		return (this.value ? "true" : "false") + " [" + this.returnValue.toString() + "]";
	}
}
