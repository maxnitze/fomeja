package de.agra.sat.koselleck.decompiling.datatypes;


/**
 * 
 * @author Max Nitze
 */
public class AbstractBooleanConstraint extends AbstractConstraint {
	/**  */
	public final boolean value;
	
	/**
	 * 
	 * @param value
	 */
	public AbstractBooleanConstraint(boolean value) {
		this.value = value;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {}
	
	/**
	 * 
	 * @param prefixedField
	 * @param replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint evaluate() {
		return this;
	}
	
	/**
	 * 
	 * @param regex
	 * 
	 * @return
	 */
	@Override
	public boolean matches(String regex) {
		return false;
	}
	
	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return false;
	}
	
	/**
	 * 
	 * @param obj
	 * 
	 * @return
	 */
	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof AbstractBooleanConstraint))
			return false;
		
		AbstractBooleanConstraint booleanConstraint = (AbstractBooleanConstraint)obj;
		
		return this.value == booleanConstraint.value;
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractBooleanConstraint clone() {
		return new AbstractBooleanConstraint(this.value);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		return this.value ? "true" : "false";
	}
}
