package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;
import de.uni_bremen.agra.fomeja.exceptions.ExpressionException;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PremMethodExpr extends PremAccessibleObjectExpr<Method> {
	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param method COMMENT
	 * @param argExprs COMMENT
	 */
	public PremMethodExpr(Expression expr, Method method, List<Expression> argExprs) {
		super(expr, method, argExprs);
		this.integrityCheck();
	}

	/** getter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Method getMethod() {
		return this.accessibleObject;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.accessibleObject.getReturnType();
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		List<Expression> evalArgExprs = new ArrayList<Expression>();
		for (Expression argExpr : this.argExprs)
			evalArgExprs.add(argExpr.evaluate(compVars));
		this.argExprs = evalArgExprs;

		this.expr = this.expr.evaluate(compVars);

		return this.handleAccessibleObject();
	}

	@Override
	public Expression simplify() {
		List<Expression> simplifiedArgExprs = new ArrayList<Expression>();
		for (Expression argExpr : this.argExprs)
			simplifiedArgExprs.add(argExpr.simplify());
		this.argExprs = simplifiedArgExprs;

		this.expr = this.expr.simplify();

		return this.handleAccessibleObject();
	}

	@Override
	public PremMethodExpr clone() {
		List<Expression> clonedArgumentExprs = new ArrayList<Expression>();
		for (Expression argumentExpr : this.argExprs)
			clonedArgumentExprs.add(argumentExpr.clone());

		return new PremMethodExpr(this.expr.clone(), this.accessibleObject, clonedArgumentExprs);
	}

	@Override
	public String toString() {
		if (Modifier.isStatic(this.accessibleObject.getModifiers()))
			return this.accessibleObject.getDeclaringClass().getSimpleName() + "." + this.accessibleObject.getName() + "(" + this.getArgumentString() + ")";
		else
			return this.expr.toString() + "." + this.accessibleObject.getName() + "(" + this.getArgumentString() + ")";
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremMethodExpr))
			return false;

		PremMethodExpr premMethodExpr = (PremMethodExpr) object;

		for (int i=0; i<this.argExprs.size(); i++)
			if (!this.argExprs.get(i).equals(premMethodExpr.argExprs.get(i)))
				return false;

		return this.expr.equals(premMethodExpr.expr)
				&& this.accessibleObject.equals(premMethodExpr.accessibleObject);
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 */
	private void integrityCheck() {
		if (!Modifier.isStatic(this.accessibleObject.getModifiers()) && !ClassUtils.isAssignable(this.accessibleObject.getDeclaringClass(), this.expr.getResultType())) {
			String message = "can not invoke method \"" + this.accessibleObject.getName() + "(" + this.getParameterTypeString() + ")\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" on expression \"" + this.expr + "\" with result type \"" + this.expr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(PremAccessibleObjectExpr.class).fatal(message);
			throw new ExpressionException(message);
		} else if (this.accessibleObject.getParameterTypes().length != this.argExprs.size()) {
			String message = "can not invoke method \"" + this.accessibleObject.getName() + "(" + this.getParameterTypeString() + ")\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" with parameters \"" + this.getArgumentString() + "\" of type \"" + this.getArgumentTypeString() + "\"";
			Logger.getLogger(PremAccessibleObjectExpr.class).fatal(message);
			throw new ExpressionException(message);
		} else {
			for (int i=0; i<this.argExprs.size(); i++) {
				if (!ClassUtils.isCastOrAssignable(this.accessibleObject.getParameterTypes()[i], this.argExprs.get(i).getResultType())) {
					String message = "can not invoke method \"" + this.accessibleObject.getName() + "(" + this.getParameterTypeString() + ")\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" with parameters \"" + this.getArgumentString() + "\" of type \"" + this.getArgumentTypeString() + "\"";
					Logger.getLogger(PremAccessibleObjectExpr.class).fatal(message);
					throw new ExpressionException(message);
				}
			}
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private String getParameterTypeString() {
		StringBuilder parameterTypeString = new StringBuilder();
		for (Class<?> parameterType : this.accessibleObject.getParameterTypes()) {
			if (parameterTypeString.length() > 0)
				parameterTypeString.append(", ");
			parameterTypeString.append(parameterType.getSimpleName().toString());
		}

		return parameterTypeString.toString();
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression handleAccessibleObject() {
		if (this.expr instanceof AtomExpr<?>
				&& ((AtomExpr<?>) this.expr).isFinishedType()) {
			Object[] arguments = new Object[this.argExprs.size()];
			for (int i=0; i<this.argExprs.size(); i++) {
				if (!(this.argExprs.get(i) instanceof AtomExpr<?>) ||
						!((AtomExpr<?>) this.argExprs.get(i)).isFinishedType())
					return this;
		
				arguments[i] = ((AtomExpr<?>) this.argExprs.get(i)).getValue();
			}

			boolean accessibility = this.accessibleObject.isAccessible();
			this.accessibleObject.setAccessible(true);
			try {
				Object invokationObject;
				if (Modifier.isStatic(this.accessibleObject.getModifiers()))
					invokationObject = null;
				else
					invokationObject = ((AtomExpr<?>) this.expr).getValue();

				if (ClassUtils.isBooleanType(this.accessibleObject.getReturnType()))
					return new AtomIntegerExpr(
							this.accessibleObject.invoke(invokationObject, arguments).equals(true) ? 1 : 0);
				else if (ClassUtils.isDoubleType(this.accessibleObject.getReturnType()))
					return new AtomDoubleExpr(
							(Double) this.accessibleObject.invoke(invokationObject, arguments));
				else if (ClassUtils.isFloatType(this.accessibleObject.getReturnType()))
					return new AtomFloatExpr(
							(Float) this.accessibleObject.invoke(invokationObject, arguments));
				else if (ClassUtils.isIntegerType(this.accessibleObject.getReturnType()))
					return new AtomIntegerExpr(
							(Integer) this.accessibleObject.invoke(invokationObject, arguments));
				else if (ClassUtils.isLongType(this.accessibleObject.getReturnType()))
					return new AtomIntegerExpr(
							((Long) this.accessibleObject.invoke(invokationObject, arguments)).intValue());
				else if (ClassUtils.isShortType(this.accessibleObject.getReturnType()))
					return new AtomIntegerExpr(
							((Short) this.accessibleObject.invoke(invokationObject, arguments)).intValue());
				else if (ClassUtils.isCharType(this.accessibleObject.getReturnType()))
					return new AtomCharacterExpr(
							(char) this.accessibleObject.invoke(invokationObject, arguments));
				else if (ClassUtils.isByteType(this.accessibleObject.getReturnType()))
					throw new RuntimeException("get expression from byte method not implemented yet"); // TODO implement
				else
					return new AtomObjectExpr(
							this.accessibleObject.invoke(invokationObject, arguments));
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
				StringBuilder argumentString = new StringBuilder();
				for (Object argument : arguments) {
					if (argumentString.length() > 0)
						argumentString.append(", ");
					argumentString.append(argument.toString());
					argumentString.append("(:");
					argumentString.append(argument.getClass().getSimpleName());
					argumentString.append(")");
				}

				String message = "could not invoke method \"" + this.accessibleObject.toGenericString() + "\" with arguments \"(" + argumentString.toString() + ")\"";
				Logger.getLogger(PremMethodExpr.class).fatal(message);
				throw new EvaluationException(message);
			} finally {
				this.accessibleObject.setAccessible(accessibility);
			}
		} else
			return this;
	}
}
