package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * AbstractBooleanConstraint represents a boolean value in a constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractBooleanConstraint extends AbstractConstraint {
	/** the boolean value */
	public final boolean value;
	
	/**
	 * Constructor for a new AbstractBooleanConstraint.
	 * 
	 * @param value the new boolean value
	 */
	public AbstractBooleanConstraint(boolean value) {
		this.value = value;
	}
	
	/**
	 * replaceAll does nothing.
	 * 
	 * @param regex is ignored
	 * @param replacement is ignored
	 */
	@Override
	public void replaceAll(String regex, String replacement) {}
	
	/**
	 * replaceAll does nothing.
	 * 
	 * @param prefixedField is ignored
	 * @param replacement is ignored
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {}
	
	/**
	 * evaluate returns this object.
	 * 
	 * @return this object
	 */
	@Override
	public AbstractConstraint evaluate() {
		return this;
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
		return false;
	}
	
	/**
	 * matches returns {@code false}.
	 * 
	 * @param prefixedField is ignored
	 * 
	 * @return {@code false}
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return false;
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
		
		return this.value == ((AbstractBooleanConstraint)object).value;
	}
	
	/**
	 * clone returns a new abstract boolean constraint with the same boolean
	 *  value.
	 * 
	 * @return a new abstract boolean constraint with the same value
	 */
	@Override
	public AbstractBooleanConstraint clone() {
		return new AbstractBooleanConstraint(this.value);
	}
	
	/**
	 * toString returns the string representation of the abstract boolean
	 *  value.
	 * 
	 * @return the string representation of the abstract boolean value
	 */
	@Override
	public String toString() {
		return this.value ? "true" : "false";
	}
}
