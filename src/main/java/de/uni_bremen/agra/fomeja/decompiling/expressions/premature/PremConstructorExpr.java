package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.lang3.builder.HashCodeBuilder;
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
public class PremConstructorExpr extends PremAccessibleObjectExpr<Constructor<?>> {
	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param constructor COMMENT
	 * @param argExprs COMMENT
	 */
	public PremConstructorExpr(Expression expr, Constructor<?> constructor, List<Expression> argExprs) {
		super(expr, constructor, argExprs);
		this.integrityCheck();
	}

	/** getter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Constructor<?> getConstructor() {
		return this.accessibleObject;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.accessibleObject.getDeclaringClass();
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

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremConstructorExpr))
			return false;

		PremConstructorExpr premConstructorExpr = (PremConstructorExpr) object;

		for (int i=0; i<this.argExprs.size(); i++)
			if (!this.argExprs.get(i).equals(premConstructorExpr.argExprs.get(i)))
				return false;

		return super.equals(premConstructorExpr)
				&& this.expr.equals(premConstructorExpr.expr)
				&& this.accessibleObject.equals(premConstructorExpr.accessibleObject);
	}

	@Override
	public int hashCode() {
		HashCodeBuilder hashCodeBuilder =  new HashCodeBuilder(43, 13)
				.appendSuper(super.hashCode())
				.append(this.expr)
				.append(this.accessibleObject);
		for (Expression argExpr : this.argExprs)
			hashCodeBuilder.append(argExpr);
		return hashCodeBuilder.toHashCode();
	}

	@Override
	public PremConstructorExpr clone() {
		List<Expression> clonedArgumentExprs = new ArrayList<Expression>();
		for (Expression argumentExpr : this.argExprs)
			clonedArgumentExprs.add(argumentExpr.clone());

		return new PremConstructorExpr(this.expr.clone(), this.accessibleObject, clonedArgumentExprs);
	}

	@Override
	public String toString() {
		return "new " + ((Class<?>) ((AtomExpr<?>) this.expr).getValue()).getName() + "(" + this.getArgumentString() + ")";
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 */
	private void integrityCheck() {
		if (!ClassUtils.isAssignable(this.accessibleObject.getDeclaringClass(), this.expr.getResultType())) {
			String message = "can not invoke constructor \"" + this.accessibleObject.getName() + "(" + this.getParameterTypeString() + ")\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" on expression \"" + this.expr + "\" with result type \"" + this.expr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(PremConstructorExpr.class).fatal(message);
			throw new ExpressionException(message);
		} else if (this.accessibleObject.getParameterTypes().length != this.argExprs.size()) {
			String message = "can not invoke constructor \"" + this.accessibleObject.getName() + "(" + this.getParameterTypeString() + ")\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" with parameters \"" + this.getArgumentString() + "\" of type \"" + this.getArgumentTypeString() + "\"";
			Logger.getLogger(PremConstructorExpr.class).fatal(message);
			throw new ExpressionException(message);
		} else {
			for (int i=0; i<this.argExprs.size(); i++) {
				if (!ClassUtils.isCastOrAssignable(this.accessibleObject.getParameterTypes()[i], this.argExprs.get(i).getResultType())) {
					String message = "can not invoke constructor \"" + this.accessibleObject.getName() + "(" + this.getParameterTypeString() + ")\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" with parameters \"" + this.getArgumentString() + "\" of type \"" + this.getArgumentTypeString() + "\"";
					Logger.getLogger(PremConstructorExpr.class).fatal(message);
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
				if (ClassUtils.isBooleanType(this.accessibleObject.getDeclaringClass()))
					return new AtomIntegerExpr(
							this.accessibleObject.newInstance(arguments).equals(true) ? 1 : 0);
				else if (ClassUtils.isDoubleType(this.accessibleObject.getDeclaringClass()))
					return new AtomDoubleExpr(
							(Double) this.accessibleObject.newInstance(arguments));
				else if (ClassUtils.isFloatType(this.accessibleObject.getDeclaringClass()))
					return new AtomFloatExpr(
							(Float) this.accessibleObject.newInstance(arguments));
				else if (ClassUtils.isIntegerType(this.accessibleObject.getDeclaringClass()))
					return new AtomIntegerExpr(
							(Integer) this.accessibleObject.newInstance(arguments));
				else if (ClassUtils.isLongType(this.accessibleObject.getDeclaringClass()))
					return new AtomIntegerExpr(
							((Long) this.accessibleObject.newInstance(arguments)).intValue());
				else if (ClassUtils.isShortType(this.accessibleObject.getDeclaringClass()))
					return new AtomIntegerExpr(
							((Short) this.accessibleObject.newInstance(arguments)).intValue());
				else if (ClassUtils.isCharType(this.accessibleObject.getDeclaringClass()))
					return new AtomCharacterExpr(
							(Character) this.accessibleObject.newInstance(arguments));
				else if (ClassUtils.isByteType(this.accessibleObject.getDeclaringClass()))
					throw new RuntimeException("get expression from byte constructor not implemented yet"); // TODO implement
				else
					return new AtomObjectExpr(
							this.accessibleObject.newInstance(arguments));
			} catch (IllegalAccessException | IllegalArgumentException | InstantiationException | InvocationTargetException e) {
				StringBuilder argumentString = new StringBuilder();
				for (Object argument : arguments) {
					if (argumentString.length() > 0)
						argumentString.append(", ");
					argumentString.append(argument.toString());
					argumentString.append("(:");
					argumentString.append(argument.getClass().getSimpleName());
					argumentString.append(")");
				}

				String message = "could not invoke constructor \"" + this.accessibleObject.toGenericString() + "\" with arguments \"(" + argumentString.toString() + ")\"";
				Logger.getLogger(PremConstructorExpr.class).fatal(message);
				throw new EvaluationException(message);
			} finally {
				this.accessibleObject.setAccessible(accessibility);
			}
		} else
			return this;
	}
}
