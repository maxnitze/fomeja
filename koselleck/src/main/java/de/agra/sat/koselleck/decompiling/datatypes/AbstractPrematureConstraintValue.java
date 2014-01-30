package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;

import org.apache.log4j.Logger;

/**
 * 
 * @author Max Nitze
 */
public class AbstractPrematureConstraintValue extends AbstractConstraintValue {
	/**  */
	public AbstractConstraintValue constraintValue;
	/**  */
	public final AccessibleObject accessibleObject;
	/**  */
	public final List<AbstractConstraintValue> objectArguments;
	
	/**
	 * 
	 * @param constraintValue
	 * @param accessibleObject
	 * @param objectArguments
	 */
	public AbstractPrematureConstraintValue(AbstractConstraintValue constraintValue, AccessibleObject accessibleObject, List<AbstractConstraintValue> objectArguments) {
		this.constraintValue = constraintValue;
		this.accessibleObject = accessibleObject;
		this.objectArguments = objectArguments;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraintValue.replaceAll(regex, replacement);
		
		for(AbstractConstraintValue methodArgument : this.objectArguments)
			methodArgument.replaceAll(regex, replacement);
	}
	
	/**
	 * 
	 * @param prefixedField
	 * @param replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		this.constraintValue.replaceAll(prefixedField, replacement);
		
		for(AbstractConstraintValue methodArgument : this.objectArguments)
			methodArgument.replaceAll(prefixedField, replacement);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintValue evaluate() {
		/** evaluate this constraint value */
		this.constraintValue = this.constraintValue.evaluate();
		/** evaluate the arguments for the arguments the method is called with */
		for(int i=0; i<this.objectArguments.size(); i++)
			this.objectArguments.set(i, this.objectArguments.get(i).evaluate());
		
		/** evaluated constraint value is a literal */
		if(this.constraintValue instanceof AbstractConstraintLiteral) {
			AbstractConstraintLiteral constraintLiteral = (AbstractConstraintLiteral)this.constraintValue;
			
			/** check for unfinished argument values */
			Object[] arguments = new Object[this.objectArguments.size()];
			for(int i=0; i<this.objectArguments.size(); i++) {
				if(!(this.objectArguments.get(i) instanceof AbstractConstraintLiteral) ||
						!((AbstractConstraintLiteral)this.objectArguments.get(i)).valueType.isFinishedType)
					return this;
				
				arguments[i] = ((AbstractConstraintLiteral)this.objectArguments.get(i)).value;
			}
			
			/** try to invoke the accessible object (method or constructor) */
			try {
				/** accessible object is a method */
				if(this.accessibleObject instanceof Method &&
						(constraintLiteral.valueType == ConstraintValueType.NULL ||
						((AbstractConstraintLiteral)this.constraintValue).valueType.hasClass(((Method)this.accessibleObject).getDeclaringClass()))) {
					Method method = (Method)this.accessibleObject;
					return new AbstractConstraintLiteral(
						method.invoke(constraintLiteral.valueType == ConstraintValueType.NULL ? null : constraintLiteral.value, this.objectArguments),
						ConstraintValueType.fromClass(method.getReturnType()), false);
				}
				/** accessible object is a constructor */
				else if(this.accessibleObject instanceof Constructor<?>) {
					Constructor<?> constructor = (Constructor<?>)this.accessibleObject;
					return new AbstractConstraintLiteral(
							constructor.newInstance(null, this.objectArguments),
							ConstraintValueType.fromClass(constructor.getDeclaringClass()), false);
				}
				/** otherwise */
				else
					return this;
					
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | InstantiationException e) {
				String message;
				if(this.accessibleObject instanceof Method)
					message = "could not invoke method \"" + ((Method)this.accessibleObject).toGenericString() + "\"";
				else if(this.accessibleObject instanceof Constructor<?>)
					message = "could not invoke constructor \"" + ((Constructor<?>)this.accessibleObject).toGenericString() + "\"";
				else
					message = "could not invoke accessible object type \"" + this.accessibleObject.toString() + "\"";
				Logger.getLogger(AbstractPrematureConstraintValue.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		} else
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
		return this.constraintValue.matches(regex);
	}
	
	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return this.constraintValue.matches(prefixedField);
	}
	
	/**
	 * 
	 * @param object
	 * 
	 * @return
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractPrematureConstraintValue))
			return false;
		
		AbstractPrematureConstraintValue constraintValue = (AbstractPrematureConstraintValue)object;
		
		return this.constraintValue.equals(constraintValue.constraintValue) &&
				this.accessibleObject == constraintValue.accessibleObject;
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintValue clone() {
		return new AbstractPrematureConstraintValue(
				this.constraintValue.clone(), this.accessibleObject, this.objectArguments);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		StringBuilder argumentString = new StringBuilder();
		for(AbstractConstraintValue argument : this.objectArguments) {
			if(argumentString.length() > 0)
				argumentString.append(", ");
			argumentString.append(argument.toString());
		}
		
		if(this.accessibleObject instanceof Method)
			return this.constraintValue.toString() + "." + ((Method)this.accessibleObject).getName() + "(" + argumentString.toString() + ")";
		else if(this.accessibleObject instanceof Constructor<?>)
			return "new " + ((Class<?>)((AbstractConstraintLiteral)this.constraintValue).value).getName() + "(" + argumentString.toString() + ")";
		else
			return this.accessibleObject.toString();
	}
}
