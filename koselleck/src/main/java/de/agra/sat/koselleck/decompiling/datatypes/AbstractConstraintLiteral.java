package de.agra.sat.koselleck.decompiling.datatypes;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownConstraintValueTypeException;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteral extends AbstractConstraintValue {
	/**  */
	public Object value;
	/**  */
	public ConstraintValueType valueType;
	/**  */
	public final boolean isVariable;
	
	/**
	 * 
	 * @param value
	 * @param valueType
	 * @param isVariable
	 */
	public AbstractConstraintLiteral(Object value, ConstraintValueType valueType, boolean isVariable) {
		if(valueType == ConstraintValueType.STRING && ((String)value).matches("\\d+")) {
			this.value = Integer.parseInt((String)value);
			this.valueType = ConstraintValueType.INTEGER;
		} else {
			this.value = value;
			this.valueType = valueType;
		}
		this.isVariable = isVariable;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		if(this.valueType == ConstraintValueType.STRING && ((String)this.value).matches(regex)) {
			if(replacement.matches("\\d+")) {
				this.value = Integer.parseInt(replacement);
				this.valueType = ConstraintValueType.INTEGER;
			} else
				((String)this.value).replaceAll(regex, replacement);
		} else if(this.valueType == ConstraintValueType.PREFIXED_FIELD && ((PrefixedField)this.value).prefixedName.matches(regex)) {
			if(replacement.matches("\\d+")) {
				this.value = Integer.parseInt(replacement);
				this.valueType = ConstraintValueType.INTEGER;
			} else {
				this.value = new String(replacement);
				this.valueType = ConstraintValueType.STRING;
			}
		}
	}
	
	/**
	 * 
	 * @param prefixedField
	 * @param replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		if(this.valueType == ConstraintValueType.PREFIXED_FIELD && ((PrefixedField)this.value).equals(prefixedField)) {
			if(replacement.matches("\\d+")) {
				this.value = Integer.parseInt(replacement);
				this.valueType = ConstraintValueType.INTEGER;
			} else {
				this.value = new String(replacement);
				this.valueType = ConstraintValueType.STRING;
			}
		}
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintValue evaluate() {
		if(this.valueType == ConstraintValueType.STRING && ((String)this.value).matches("\\d+")) {
			this.value = Integer.parseInt((String)this.value);
			this.valueType = ConstraintValueType.INTEGER;
		} else if(this.valueType == ConstraintValueType.PREFIXED_FIELD && ((PrefixedField)this.value).prefixedName.matches("\\d+")) {
			this.value = Integer.parseInt(((PrefixedField)this.value).prefixedName);
			this.valueType = ConstraintValueType.INTEGER;
		}
		
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
		if(this.valueType == ConstraintValueType.STRING)
			return ((String)this.value).matches(regex);
		else if(this.valueType == ConstraintValueType.PREFIXED_FIELD)
			return (((PrefixedField)this.value).prefixedName).matches(regex);
		else
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
		if(this.valueType == ConstraintValueType.PREFIXED_FIELD)
			return (((PrefixedField)this.value).prefixedName).matches(prefixedField.prefixedName);
		else
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
		if(!(obj instanceof AbstractConstraintLiteral))
			return false;
		
		AbstractConstraintLiteral constraintValue = (AbstractConstraintLiteral)obj;
		
		return this.value.equals(constraintValue.value);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintLiteral clone() {
		return new AbstractConstraintLiteral(
				this.value,
				this.valueType,
				this.isVariable);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		switch(this.valueType) {
		case INTEGER:
		case STRING:
			return this.value.toString();
		case PREFIXED_FIELD:
			return ((PrefixedField)this.value).prefieldsPrefixedName;
		default:
			Logger.getLogger(AbstractConstraintLiteral.class).fatal("constraint value type " + (this.valueType == null ? "null" : "\"" + this.valueType.name + "\"") + " is not known");
			throw new UnknownConstraintValueTypeException(this.valueType);
		}
	}
}
