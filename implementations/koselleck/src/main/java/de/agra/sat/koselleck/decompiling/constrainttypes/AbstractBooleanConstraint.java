package de.agra.sat.koselleck.decompiling.constrainttypes;

import java.util.Map;

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
	public final boolean value;
	/** the return value of the method evaluated to {@code value} */
	public AbstractConstraintValue returnValue;
	
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
	 * replaceAll does nothing.
	 * 
	 * @param regex is ignored
	 * @param replacement is ignored
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.returnValue.replaceAll(regex, replacement);
	}
	
	/**
	 * evaluate returns this object.
	 * 
	 * @return this object
	 */
	@Override
	public AbstractConstraint evaluate() {
		this.returnValue = this.returnValue.evaluate();
		
		return this;
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
	}
	
	/**
	 * matches returns {@code false}.
	 * 
	 * @param regex is ignored
	 * 
	 * @return {@code false}
	 */
	@Override
	public boolean matches(String regex) {
		return this.returnValue.matches(regex);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint invert() {
		return this;
	}
	
	/**
	 * equals tests if this abstract boolean constraint and the given object
	 *  are equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object is an abstract boolean
	 *  constraint and the values are equal, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractBooleanConstraint))
			return false;
		
		AbstractBooleanConstraint booleanConstraint = (AbstractBooleanConstraint)object;
		
		return this.value == booleanConstraint.value &&
				this.returnValue.equals(booleanConstraint.returnValue);
	}
	
	/**
	 * clone returns a new abstract boolean constraint with the same boolean
	 *  value.
	 * 
	 * @return a new abstract boolean constraint with the same value
	 */
	@Override
	public AbstractBooleanConstraint clone() {
		return new AbstractBooleanConstraint(this.value, this.returnValue);
	}
	
	/**
	 * toString returns the string representation of the abstract boolean
	 *  value.
	 * 
	 * @return the string representation of the abstract boolean value
	 */
	@Override
	public String toString() {
		return (this.value ? "true" : "false") + " [" + this.returnValue.toString() + "]";
	}
}
