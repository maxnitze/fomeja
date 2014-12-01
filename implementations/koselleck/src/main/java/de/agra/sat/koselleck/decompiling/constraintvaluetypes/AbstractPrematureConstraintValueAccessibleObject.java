package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AbstractPrematureConstraintValueAccessibleObject extends AbstractConstraintValue {
	/** COMMENT */
	private AbstractConstraintValue constraintValue;
	/** COMMENT */
	private final AccessibleObject accessibleObject;
	/** COMMENT */
	private final List<AbstractConstraintValue> objectArguments;

	/**
	 * COMMENT
	 * 
	 * @param constraintValue
	 * @param accessibleObject
	 * @param objectArguments
	 */
	public AbstractPrematureConstraintValueAccessibleObject(AbstractConstraintValue constraintValue, AccessibleObject accessibleObject, List<AbstractConstraintValue> objectArguments) {
		super(constraintValue.getFieldCodeIndex(), constraintValue.getOpcode(), constraintValue.getPreFieldList());
		this.constraintValue = constraintValue;
		this.accessibleObject = accessibleObject;
		this.objectArguments = objectArguments;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public AbstractConstraintValue getConstraintValue() {
		return this.constraintValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public AccessibleObject getAccessibleObject() {
		return this.accessibleObject;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<AbstractConstraintValue> getObjectArguments() {
		return this.objectArguments;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraintValue.replaceAll(regex, replacement);

		for (AbstractConstraintValue methodArgument : this.objectArguments)
			methodArgument.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraintValue evaluate() {
		/** evaluate this constraint value */
		this.constraintValue = this.constraintValue.evaluate();
		/** evaluate the arguments for the arguments the method is called with */
		for (int i=0; i<this.objectArguments.size(); i++)
			this.objectArguments.set(i, this.objectArguments.get(i).evaluate());

		/** evaluated constraint value is a literal */
		if (this.constraintValue instanceof AbstractConstraintLiteral<?>) {
			AbstractConstraintLiteral<?> constraintLiteral = (AbstractConstraintLiteral<?>) this.constraintValue;

			/** check for unfinished argument values */
			Object[] arguments = new Object[this.objectArguments.size()];
			for (int i = 0; i < this.objectArguments.size(); i++) {
				if (!(this.objectArguments.get(i) instanceof AbstractConstraintLiteral<?>) ||
						!((AbstractConstraintLiteral<?>) this.objectArguments.get(i)).isFinishedType())
					return this;

				arguments[i] = ((AbstractConstraintLiteral<?>) this.objectArguments.get(i)).getValue();
			}

			/** try to invoke the accessible object (method or constructor) */
			try {
				if (this.accessibleObject instanceof Method) {
					Method method = (Method) this.accessibleObject;

					Object invokationObject;
					if (Modifier.isStatic(method.getModifiers()))
						invokationObject = null;
					else
						invokationObject = constraintLiteral.getValue();

					if (ClassUtils.isDoubleClass(method.getReturnType()))
						return new AbstractConstraintLiteralDouble(
								(Double) method.invoke(invokationObject, arguments));
					else if (ClassUtils.isFloatClass(method.getReturnType()))
						return new AbstractConstraintLiteralFloat(
								(Float) method.invoke(invokationObject, arguments));
					else if (ClassUtils.isIntegerClass(method.getReturnType()))
						return new AbstractConstraintLiteralInteger(
								(Integer) method.invoke(invokationObject, arguments));
					else if (ClassUtils.isBooleanClass(method.getReturnType()))
						return new AbstractConstraintLiteralInteger(
								method.invoke(invokationObject, arguments).equals(true) ? 1 : 0);
					else
						return new AbstractConstraintLiteralObject(
								method.invoke(invokationObject, arguments));
				}
				/** accessible object is a constructor */
				else if (this.accessibleObject instanceof Constructor<?>) {
					Constructor<?> constructor = (Constructor<?>)this.accessibleObject;

					if (ClassUtils.isDoubleClass(
							constructor.getDeclaringClass()))
						return new AbstractConstraintLiteralDouble(
								(Double) constructor.newInstance(arguments));
					else if (ClassUtils.isFloatClass(
							constructor.getDeclaringClass()))
						return new AbstractConstraintLiteralFloat(
								(Float) constructor.newInstance(arguments));
					else if (ClassUtils.isIntegerClass(
							constructor.getDeclaringClass()))
						return new AbstractConstraintLiteralInteger(
								(Integer) constructor.newInstance(arguments));
					else
						return new AbstractConstraintLiteralObject(
								constructor.newInstance(arguments));
				}
				/** otherwise */
				else
					return this;

			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | InstantiationException e) {
				StringBuilder argumentString = new StringBuilder();
				for (Object argument : arguments) {
					if (argumentString.length() > 0)
						argumentString.append(", ");
					argumentString.append(argument.toString());
					argumentString.append("(:");
					argumentString.append(argument.getClass());
					argumentString.append(")");
				}

				String message;
				if (this.accessibleObject instanceof Method)
					message = "could not invoke method \"" + ((Method) this.accessibleObject).toGenericString() + "\" with arguments \"(" + argumentString.toString() + ")\"";
				else if (this.accessibleObject instanceof Constructor<?>)
					message = "could not invoke constructor \"" + ((Constructor<?>) this.accessibleObject).toGenericString() + "\" with arguments \"(" + argumentString.toString() + ")\"";
				else
					message = "could not invoke accessible object type \"" + this.accessibleObject.toString() + "\" with arguments \"(" + argumentString.toString() + ")\"";
				Logger.getLogger(AbstractPrematureConstraintValueAccessibleObject.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		} else
			return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		this.constraintValue = this.constraintValue.substitute(constraintArguments);

		for (int i=0; i<this.objectArguments.size(); i++)
			this.objectArguments.set(i, this.objectArguments.get(i).substitute(constraintArguments));

		return this;
	}

	@Override
	public boolean matches(String regex) {
		return this.constraintValue.matches(regex);
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiterals = new HashSet<AbstractConstraintLiteral<?>>();
		unfinishedConstraintLiterals.addAll(this.constraintValue.getUnfinishedConstraintLiterals());
		for (AbstractConstraintValue objectArgument : this.objectArguments)
			unfinishedConstraintLiterals.addAll(objectArgument.getUnfinishedConstraintLiterals());

		return unfinishedConstraintLiterals;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractPrematureConstraintValueAccessibleObject))
			return false;

		AbstractPrematureConstraintValueAccessibleObject constraintValue = (AbstractPrematureConstraintValueAccessibleObject)object;

		return this.constraintValue.equals(constraintValue.constraintValue) &&
				this.accessibleObject == constraintValue.accessibleObject;
	}

	@Override
	public AbstractConstraintValue clone() {
		List<AbstractConstraintValue> clonedObjectArguments = new ArrayList<AbstractConstraintValue>();
		for (AbstractConstraintValue objectArgument : this.objectArguments)
			clonedObjectArguments.add(objectArgument.clone());

		return new AbstractPrematureConstraintValueAccessibleObject(
				this.constraintValue.clone(), this.accessibleObject, clonedObjectArguments);
	}

	@Override
	public String toString() {
		StringBuilder argumentString = new StringBuilder();
		for (AbstractConstraintValue argument : this.objectArguments) {
			if (argumentString.length() > 0)
				argumentString.append(", ");
			argumentString.append(argument.toString());
		}

		if (this.accessibleObject instanceof Method)
			return this.constraintValue.toString() + "." + ((Method)this.accessibleObject).getName() + "(" + argumentString.toString() + ")";
		else if (this.accessibleObject instanceof Constructor<?>)
			return "new " + ((Class<?>)((AbstractConstraintLiteral<?>)this.constraintValue).getValue()).getName() + "(" + argumentString.toString() + ")";
		else
			return this.accessibleObject.toString();
	}
}
