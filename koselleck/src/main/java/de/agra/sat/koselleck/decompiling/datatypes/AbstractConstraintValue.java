package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public abstract class AbstractConstraintValue {
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	public abstract void replaceAll(String regex, String replacement);

	/**
	 * 
	 * @param prefixedField
	 * @param replacement
	 */
	public abstract void replaceAll(PrefixedField prefixedField, String replacement);
	
	/**
	 * 
	 * @return
	 */
	public abstract AbstractConstraintValue evaluate();
	
	/**
	 * 
	 * @param regex
	 * 
	 * @return
	 */
	public abstract boolean matches(String regex);
	
	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	public abstract boolean matches(PrefixedField prefixedField);
	
	/**
	 * 
	 * @param object
	 * 
	 * @return
	 */
	@Override
	public abstract boolean equals(Object object);
	
	/**
	 * 
	 * @return
	 */
	@Override
	public abstract AbstractConstraintValue clone();
	
	/**
	 * 
	 * @return
	 */
	@Override
	public abstract String toString();
}
