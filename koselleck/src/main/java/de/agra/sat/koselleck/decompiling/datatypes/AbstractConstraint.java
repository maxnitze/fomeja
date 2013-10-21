package de.agra.sat.koselleck.decompiling.datatypes;

import java.util.HashSet;
import java.util.Set;

/**
 * 
 * @author Max Nitze
 */
public abstract class AbstractConstraint implements Cloneable {
	/**  */
	public final Set<PrefixedField> prefixedFields;
	
	/**
	 * 
	 */
	public AbstractConstraint() {
		this.prefixedFields = new HashSet<PrefixedField>();
	}
	
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
	public abstract AbstractConstraint evaluate();
	
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
	 * @param obj
	 * 
	 * @return
	 */
	@Override
	public abstract boolean equals(Object obj);
	
	/**
	 * 
	 * @return
	 */
	@Override
	public abstract AbstractConstraint clone();
	
	/**
	 * 
	 * @return
	 */
	@Override
	public abstract String toString();
}
