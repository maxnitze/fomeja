package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * AbstractConstraint is an abstract class for all types of constraints.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AbstractConstraint implements Cloneable {
	/** the set of prefixed fields of the constraint */
	public final Set<PrefixedField> prefixedFields;
	
	/**
	 * Constructor for a new abstract constraint.
	 * 
	 * @param prefiexedFields the prefixed fields for this abstract constraint
	 */
	public AbstractConstraint(List<PrefixedField> prefixedFields) {
		this.prefixedFields = new HashSet<PrefixedField>(prefixedFields);
	}
	
	/**
	 * replaceAll replaces all occurrences of the string {@code regex} with the
	 *  replacement string {@code replacement}.
	 * 
	 * @param regex the string to replace
	 * @param replacement the replacement
	 */
	public abstract void replaceAll(String regex, String replacement);
	
	/**
	 * replaceAll replaces all occurrences of the prefixed field
	 *  {@code prefixedField} with the replacement string {@code replacement}.
	 * 
	 * @param prefixedField the prefixed field to replace
	 * @param replacement the replacement
	 */
	public abstract void replaceAll(PrefixedField prefixedField, String replacement);
	
	/**
	 * evaluate evaluates the abstract constraint.
	 * 
	 * @return the evaluated abstract constraint
	 */
	public abstract AbstractConstraint evaluate();
	
	/**
	 * matches checks if any part of this abstract constraint matches the
	 *  string {@code regex}.
	 * 
	 * @param regex the string to check for
	 * 
	 * @return {@code true} if the abstract constraint contains the string
	 *  {@code regex}, {@code false} otherwise
	 */
	public abstract boolean matches(String regex);
	
	/**
	 * matches checks if any part of this abstract constraint matches the
	 *  prefixed field {@code prefixedField}.
	 * 
	 * @param prefixedField the prefied field to check for
	 * 
	 * @return {@code true} if the abstract constraint contains the prefixed
	 *  field {@code prefixedField}, {@code false} otherwise
	 */
	public abstract boolean matches(PrefixedField prefixedField);
	
	/**
	 * invert inverts this abstract constraint.
	 * 
	 * @return the inverted abstract constraint
	 */
	public abstract AbstractConstraint invert();
	
	/**
	 * equals checks if this abstract constraint and the given object are
	 *  equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object an this abstract constraint are
	 *  equal, {@code false} otherwise
	 */
	@Override
	public abstract boolean equals(Object object);
	
	/**
	 * clone returns a copy of this abstract constraint.
	 * 
	 * @return a copy of this abstract constraint
	 */
	@Override
	public abstract AbstractConstraint clone();
	
	/**
	 * toString returns a string representation of this abstract constraint.
	 * 
	 * @return the string representation of this abstract constraint
	 */
	@Override
	public abstract String toString();
}
