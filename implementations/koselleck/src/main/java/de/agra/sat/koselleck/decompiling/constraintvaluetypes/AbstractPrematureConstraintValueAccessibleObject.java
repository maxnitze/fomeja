package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.utils.CompareUtils;

/**
 * 
 * @author Max Nitze
 */
public class AbstractPrematureConstraintValueAccessibleObject extends AbstractConstraintValue {
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
	public AbstractPrematureConstraintValueAccessibleObject(AbstractConstraintValue constraintValue, AccessibleObject accessibleObject, List<AbstractConstraintValue> objectArguments) {
		this.constraintValue = constraintValue;
		this.accessibleObject = accessibleObject;
		this.objectArguments = objectArguments;
	}

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
						!((AbstractConstraintLiteral<?>) this.objectArguments.get(i)).isFinishedType)
					return this;

				arguments[i] = ((AbstractConstraintLiteral<?>) this.objectArguments.get(i)).value;
			}

			/** try to invoke the accessible object (method or constructor) */
			try {
				if (this.accessibleObject instanceof Method) {
					Method method = (Method) this.accessibleObject;

					Object invokationObject;
					if (Modifier.isStatic(method.getModifiers()))
						invokationObject = null;
					else
						invokationObject = constraintLiteral.value;

					if (CompareUtils.equalsAny(method.getReturnType(), CompareUtils.doubleClasses))
						return new AbstractConstraintLiteralDouble(
								(Double) method.invoke(invokationObject, arguments));
					else if (CompareUtils.equalsAny(method.getReturnType(), CompareUtils.floatClasses))
						return new AbstractConstraintLiteralFloat(
								(Float) method.invoke(invokationObject, arguments));
					else if (CompareUtils.equalsAny(method.getReturnType(), CompareUtils.integerClasses))
						return new AbstractConstraintLiteralInteger(
								(Integer) method.invoke(invokationObject, arguments));
					else if (CompareUtils.equalsAny(method.getReturnType(), CompareUtils.booleanClasses))
						return new AbstractConstraintLiteralInteger(
								method.invoke(invokationObject, arguments).equals(true) ? 1 : 0);
					else
						return new AbstractConstraintLiteralObject(
								method.invoke(invokationObject, arguments));
				}
				/** accessible object is a constructor */
				else if (this.accessibleObject instanceof Constructor<?>) {
					Constructor<?> constructor = (Constructor<?>)this.accessibleObject;

					if (CompareUtils.equalsAny(
							constructor.getDeclaringClass(), CompareUtils.doubleClasses))
						return new AbstractConstraintLiteralDouble(
								(Double) constructor.newInstance(arguments));
					else if (CompareUtils.equalsAny(
							constructor.getDeclaringClass(), CompareUtils.floatClasses))
						return new AbstractConstraintLiteralFloat(
								(Float) constructor.newInstance(arguments));
					else if (CompareUtils.equalsAny(
							constructor.getDeclaringClass(), CompareUtils.integerClasses))
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

		for (int i = 0; i < this.objectArguments.size(); i++)
			this.objectArguments.set(i, this.objectArguments.get(i).substitute(constraintArguments));

		return this;
	}

	@Override
	public boolean matches(String regex) {
		return this.constraintValue.matches(regex);
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
			return "new " + ((Class<?>)((AbstractConstraintLiteral<?>)this.constraintValue).value).getName() + "(" + argumentString.toString() + ")";
		else
			return this.accessibleObject.toString();
	}
}