package de.agra.sat.koselleck.decompiling.constrainttypes;

/**
 * AbstractConstraint is an abstract class for all types of constraint values.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AbstractConstraintValue {
	public static AbstractConstraintValue NULLValue = new AbstractConstraintLiteralObject(null);

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
