package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.Field;
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
public class PremFieldExpr extends PremAccessibleObjectExpr<Field> {
	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param field COMMENT
	 */
	public PremFieldExpr(Expression expr, Field field) {
		super(expr, field, new ArrayList<Expression>());
		this.integrityCheck();
	}

	/** getter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Field getField() {
		return this.accessibleObject;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.accessibleObject.getType();
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
		List<Expression> evalArgExprs = new ArrayList<Expression>();
		for (Expression argExpr : this.argExprs)
			evalArgExprs.add(argExpr.simplify());
		this.argExprs = evalArgExprs;

		this.expr = this.expr.simplify();

		return this.handleAccessibleObject();
	}

	@Override
	public PremFieldExpr clone() {
		return new PremFieldExpr(this.expr.clone(), this.accessibleObject);
	}

	@Override
	public String toString() {
		return this.expr.toString() + "." + this.accessibleObject.getName();
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremFieldExpr))
			return false;

		PremFieldExpr premFieldExpr = (PremFieldExpr) object;

		return this.expr.equals(premFieldExpr.expr)
				&& this.accessibleObject.equals(premFieldExpr.accessibleObject);
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 */
	private void integrityCheck() {
		if (!ClassUtils.isAssignable(this.accessibleObject.getDeclaringClass(), this.expr.getResultType())) {
			String message = "can not get field \"" + this.accessibleObject.getName() + "\" declared by class \"" + this.accessibleObject.getDeclaringClass().getSimpleName() + "\" from expression \"" + this.expr + "\" with result type \"" + this.expr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(PremFieldExpr.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression handleAccessibleObject() {
		if (this.expr instanceof AtomExpr<?>
				&& ((AtomExpr<?>) this.expr).isFinishedType()) {
			boolean accessibility = this.accessibleObject.isAccessible();
			this.accessibleObject.setAccessible(true);
			try {
				Object invokationObject;
				if (Modifier.isStatic(this.accessibleObject.getModifiers()))
					invokationObject = null;
				else
					invokationObject = ((AtomExpr<?>) this.expr).getValue();

				if (ClassUtils.isBooleanType(this.accessibleObject.getType()))
					return new AtomIntegerExpr(this.accessibleObject.get(invokationObject).equals(true) ? 1 : 0);
				else if (ClassUtils.isDoubleType(this.accessibleObject.getType()))
					return new AtomDoubleExpr((Double) this.accessibleObject.get(invokationObject));
				else if (ClassUtils.isFloatType(this.accessibleObject.getType()))
					return new AtomFloatExpr((Float) this.accessibleObject.get(invokationObject));
				else if (ClassUtils.isIntegerType(this.accessibleObject.getType()))
					return new AtomIntegerExpr((Integer) this.accessibleObject.get(invokationObject));
				else if (ClassUtils.isLongType(this.accessibleObject.getType()))
					return new AtomIntegerExpr(((Long) this.accessibleObject.get(invokationObject)).intValue());
				else if (ClassUtils.isShortType(this.accessibleObject.getType()))
					return new AtomIntegerExpr(((Short) this.accessibleObject.get(invokationObject)).intValue());
				else if (ClassUtils.isCharType(this.accessibleObject.getType()))
					return new AtomCharacterExpr((Character) this.accessibleObject.get(invokationObject));
				else if (ClassUtils.isByteType(this.accessibleObject.getType()))
					throw new RuntimeException("get expression from byte field not implemented yet"); // TODO implement
				else
					return new AtomObjectExpr(this.accessibleObject.get(invokationObject));
			} catch (IllegalAccessException | IllegalArgumentException e) {
				String message = "could not get field \"" + this.accessibleObject.getName() + "\" from expression \"" + this.expr + "\"";
				Logger.getLogger(PremFieldExpr.class).fatal(message);
				throw new EvaluationException(message);
			} finally {
				this.accessibleObject.setAccessible(accessibility);
			}
		} else
			return this;
	}
}
