package de.agra.sat.koselleck.decompiling.datatypes;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintValueTypeException;

/**
 * AbstractConstraintLiteral represents a literal in a constraint value.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractConstraintLiteral extends AbstractConstraintValue implements Comparable<AbstractConstraintLiteral> {
	/** the object */
	public Object value;
	/** the type of the object */
	public ConstraintValueType valueType;
	/** flag if the value is variable */
	public final boolean isVariable;
	
	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param value the new value
	 * @param valueType the new type of the value
	 * @param isVariable the new variable flag for the value
	 */
	public AbstractConstraintLiteral(Object value, ConstraintValueType valueType, boolean isVariable) {
		if(valueType == ConstraintValueType.String && ((String)value).matches("\\d+")) {
			this.value = Integer.parseInt((String)value);
			this.valueType = ConstraintValueType.Integer;
		} else {
			this.value = value;
			this.valueType = valueType;
		}
		this.isVariable = isVariable;
	}
	
	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param value the new boolean value (false --> 0, true --> 1)
	 */
	public AbstractConstraintLiteral(boolean value) {
		this.value = value ? 1 : 0;
		this.valueType = ConstraintValueType.Integer;
		this.isVariable = false;
	}
	
	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param prefixedField the new prefixed field
	 */
	public AbstractConstraintLiteral(PrefixedField prefixedField) {
		this.value = prefixedField;
		this.valueType = ConstraintValueType.PrefixedField;
		this.isVariable = prefixedField.isVariable;
	}
	
	/**
	 * replaceAll replaces all occurrences of the given regular expression
	 *  {@code regex} with the given {@code replacement}. if the replacement is
	 *  an integer type the type of this literal is changed to integer.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		if(this.valueType == ConstraintValueType.String && ((String)this.value).matches(regex)) {
			if(replacement.matches("\\d+")) {
				this.value = Integer.parseInt(replacement);
				this.valueType = ConstraintValueType.Integer;
			} else
				((String)this.value).replaceAll(regex, replacement);
		} else if(this.valueType == ConstraintValueType.PrefixedField && ((PrefixedField)this.value).prefixedName.matches(regex)) {
			if(replacement.matches("\\d+")) {
				this.value = Integer.parseInt(replacement);
				this.valueType = ConstraintValueType.Integer;
			} else {
				this.value = new String(replacement);
				this.valueType = ConstraintValueType.String;
			}
		}
	}
	
	/**
	 * replaceAll replaces all occurrences of the given prefixed field
	 *  {@code prefixedField} with the given {@code replacement}. if the
	 *  replacement is an integer type the type of this literal is changed to
	 *  integer.
	 * 
	 * @param prefixedField the prefixed field to look for
	 * @param replacement the replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		if(this.valueType == ConstraintValueType.PrefixedField && ((PrefixedField)this.value).equals(prefixedField)) {
			if(replacement.matches("\\d+")) {
				this.value = Integer.parseInt(replacement);
				this.valueType = ConstraintValueType.Integer;
			} else {
				this.value = new String(replacement);
				this.valueType = ConstraintValueType.String;
			}
		}
	}
	
	/**
	 * If the value of the literal is parsable to integer evaluate parses it.
	 *  Afterwards this abstract constraint literal is returned.
	 * 
	 * @return this abstract constraint literal
	 */
	@Override
	public AbstractConstraintValue evaluate() {
		if(this.value != null && this.valueType == ConstraintValueType.String && ((String)this.value).matches("\\d+")) {
			this.value = Integer.parseInt((String)this.value);
			this.valueType = ConstraintValueType.Integer;
		} else if(this.value != null && this.valueType == ConstraintValueType.PrefixedField && ((PrefixedField)this.value).prefixedName.matches("\\d+")) {
			this.value = Integer.parseInt(((PrefixedField)this.value).prefixedName);
			this.valueType = ConstraintValueType.Integer;
		}
		
		return this;
	}
	
	/**
	 * matches checks whether the value matches the given regular expression
	 *  {@code regex}.
	 * 
	 * @param regex the regular expression to look for
	 * 
	 * @return {@code true} if the value matches the given regular expression,
	 *  {@code false} otherwise
	 */
	@Override
	public boolean matches(String regex) {
		if(this.valueType == ConstraintValueType.String)
			return ((String)this.value).matches(regex);
		else if(this.valueType == ConstraintValueType.PrefixedField)
			return (((PrefixedField)this.value).prefixedName).matches(regex);
		else
			return false;
	}
	
	/**
	 * matches checks whether the value matches the given prefixed field
	 *  {@code prefixedField}.
	 * 
	 * @param prefixedField the prefixed field to look for
	 * 
	 * @return {@code true} if the value matches the given prefixed field,
	 *  {@code false} otherwise
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		if(this.valueType == ConstraintValueType.PrefixedField)
			return (((PrefixedField)this.value).prefixedName).matches(prefixedField.prefixedName);
		else
			return false;
	}
	
	/**
	 * equals checks if this abstract constraint literal and the given object
	 *  are equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object an this abstract constraint
	 *  literal are equal, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractConstraintLiteral))
			return false;
		
		AbstractConstraintLiteral constraintValue = (AbstractConstraintLiteral)object;
		
		return this.value.equals(constraintValue.value) &&
				this.valueType == constraintValue.valueType;
	}
	
	/**
	 * clone returns a copy of this abstract constraint literal.
	 * 
	 * @return a copy of this abstract constraint literal
	 */
	@Override
	public AbstractConstraintLiteral clone() {
		return new AbstractConstraintLiteral(
				this.value,
				this.valueType,
				this.isVariable);
	}
	
	/**
	 * toString returns the string representation of this abstract constraint
	 *  literal.
	 * 
	 * @return the string representation of this abstract constraint literal
	 */
	@Override
	public String toString() {
		switch(this.valueType) {
		case Integer:
		case Double:
		case Float:
		case String:
			return this.value.toString();
		case PrefixedField:
			return ((PrefixedField)this.value).prefixedName;
		case PrefixedClass:
			return ((PrefixedClass)this.value).clazz.getSimpleName();
		case NULL:
			return "NULL";
		default:
			Logger.getLogger(AbstractConstraintLiteral.class).fatal("constraint value type " + (this.valueType == null ? "null" : "\"" + this.valueType.name + "\"") + " is not known");
			throw new UnknownConstraintValueTypeException(this.valueType);
		}
	}
	
	/**
	 * compareTo compares this abstract constraint literal to the given one. if
	 *  this or the given abstract constraint literal has no comparable number
	 *  type an exception is thrown.
	 * 
	 * @param constraintLiteral the abstract constraint literal to compare to
	 * 
	 * @return 0 if the comparable number type of this and the given abstract
	 *  constraint literal are equal, 1 if this or -1 if the given is greater
	 */
	@Override
	public int compareTo(AbstractConstraintLiteral constraintLiteral) {
		switch(this.valueType) {
		case Double:
		case Float:
		case Integer:
			switch(constraintLiteral.valueType) {
			case Double:
			case Float:
			case Integer:
				return ((Double)this.value).compareTo((Double)constraintLiteral.value);
			default:
				NoComparableNumberTypeException exception = new NoComparableNumberTypeException(constraintLiteral);
				Logger.getLogger(AbstractConstraintLiteral.class).fatal(exception.getMessage());
				throw exception;
			}
		default:
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintLiteral.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
