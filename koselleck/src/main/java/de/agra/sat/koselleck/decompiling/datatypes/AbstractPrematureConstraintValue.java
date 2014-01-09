package de.agra.sat.koselleck.decompiling.datatypes;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.decompiling.Decompiler;
/** imports */

/**
 * 
 * @author Max Nitze
 */
public class AbstractPrematureConstraintValue extends AbstractConstraintValue {
	/**  */
	public AbstractConstraintValue constraintValue;
	/**  */
	public final Method method;
	/**  */
	public final List<AbstractConstraintValue> methodArguments;
	
	/**
	 * 
	 * @param constraintValue
	 * @param method
	 * @param methodArguments
	 */
	public AbstractPrematureConstraintValue(AbstractConstraintValue constraintValue, Method method, List<AbstractConstraintValue> methodArguments) {
		this.constraintValue = constraintValue;
		this.method = method;
		this.methodArguments = methodArguments;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraintValue.replaceAll(regex, replacement);
		
		for(AbstractConstraintValue methodArgument : this.methodArguments)
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
		
		for(AbstractConstraintValue methodArgument : this.methodArguments)
			methodArgument.replaceAll(prefixedField, replacement);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintValue evaluate() {
		this.constraintValue = this.constraintValue.evaluate();
		
		Object[] arguments = new Object[this.methodArguments.size()];
		for(int i=0; i<this.methodArguments.size(); i++) {
			if(!((AbstractConstraintLiteral)this.methodArguments.get(i)).valueType.isFinishedType)
				return this;
			
			arguments[i] = ((AbstractConstraintLiteral)this.methodArguments.get(i)).value;
		}
		
		if(this.constraintValue instanceof AbstractConstraintLiteral &&
				((AbstractConstraintLiteral)this.constraintValue).valueType.clazz.equals(this.method.getDeclaringClass())) {
			AbstractConstraintLiteral constraintLiteral = (AbstractConstraintLiteral)this.constraintValue;
			try {
				return new AbstractConstraintLiteral(
						this.method.invoke(constraintLiteral.value, this.methodArguments),
						ConstraintValueType.fromClass(this.method.getReturnType()), false);
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
				StringBuilder argumentsString = new StringBuilder();
				for(Object argument : this.methodArguments) {
					if(argumentsString.length() != 0)
						argumentsString.append(", ");
					argumentsString.append(argument);
				}
				
				String message = "could not invoke method \"" + method.getName() +"(" + argumentsString.toString() + ")\"";
				Logger.getLogger(Decompiler.class).fatal(message);
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
				this.method == constraintValue.method;
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintValue clone() {
		return new AbstractPrematureConstraintValue(
				this.constraintValue.clone(), this.method, this.methodArguments);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		return this.constraintValue.toString();
	}
}
