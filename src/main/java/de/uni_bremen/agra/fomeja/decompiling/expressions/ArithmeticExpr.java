package de.uni_bremen.agra.fomeja.decompiling.expressions;

/* import */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

/** imports */


import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.exceptions.ExpressionException;
import de.uni_bremen.agra.fomeja.exceptions.NotConvertibleException;
import de.uni_bremen.agra.fomeja.types.ArithmeticOperator;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class ArithmeticExpr extends Expression {
	/** the first expression */
	private Expression expr1;
	/** the second expression */
	private Expression expr2;
	/** the arithmetic operator */
	private final ArithmeticOperator operator;

	/**
	 * Constructor for a new arithmetic expression.
	 * 
	 * @param expr1 the new first expression
	 * @param operator the new arithmetic operator
	 * @param expr2 the new second expression
	 */
	public ArithmeticExpr(Expression expr1, ArithmeticOperator operator, Expression expr2) {
		this.expr1 = expr1;
		this.operator = operator;
		this.expr2 = expr2;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Expression getExpr1() {
		return this.expr1;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Expression getExpr2() {
		return this.expr2;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ArithmeticOperator getOperator() {
		return this.operator;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		Class<?> value1Class = this.expr1.getResultType();
		if (!ClassUtils.isBasicNumberType(value1Class)) {
			String message = "\"" + this.expr1 + "\" is not calculatable";
			Logger.getLogger(AtomExpr.class).fatal(message);
			throw new ExpressionException(message);
		}

		Class<?> value2Class = this.expr2.getResultType();
		if (!ClassUtils.isBasicNumberType(value2Class)) {
			String message = "\"" + this.expr2 + "\" is not calculatable";
			Logger.getLogger(AtomExpr.class).fatal(message);
			throw new ExpressionException(message);
		}

		if (ClassUtils.isDoubleType(value1Class) || ClassUtils.isDoubleType(value2Class))
			return Double.class;
		else if (ClassUtils.isFloatType(value1Class) || ClassUtils.isFloatType(value2Class))
			return Float.class;
		else
			return Integer.class;
	}

	@Override
	public boolean matches(String regex) {
		return this.expr1.matches(regex) || this.expr2.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.expr1.replaceAll(regex, replacement);
		this.expr2.replaceAll(regex, replacement);
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		this.expr1 = this.expr1.substitude(exprs);
		this.expr2 = this.expr2.substitude(exprs);
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		this.expr1 = this.expr1.evaluate(compVars);
		this.expr2 = this.expr2.evaluate(compVars);
		return this.handleArithmetic();
	}

	@Override
	public Expression simplify() {
		this.expr1 = this.expr1.simplify();
		this.expr2 = this.expr2.simplify();
		return this.handleArithmetic();
	}

	@Override
	public boolean isBoolExpr() {
		return false;
	}

	@Override
	public BoolExpression toBoolExpr() {
		String message = "can not convert arithmetic expression \"" + this.toString() + "\" to bool expression";
		Logger.getLogger(ArithmeticExpr.class).fatal(message);
		throw new NotConvertibleException(message);
	}

	@Override
	public boolean isUnfinished() {
		return this.expr1.isUnfinished() || this.expr2.isUnfinished();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		requiredAtomExprs.addAll(this.expr1.getRequiredAtomExprs(isRequired, compVars));
		requiredAtomExprs.addAll(this.expr2.getRequiredAtomExprs(isRequired, compVars));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return this.expr1.hasAtomVoidExprs() || this.expr2.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		atomVoidExprs.addAll(this.expr1.getAtomVoidExprs());
		atomVoidExprs.addAll(this.expr2.getAtomVoidExprs());
		return atomVoidExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.expr1.hasAtomStringExprs() || this.expr2.hasAtomStringExprs();
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		return this.expr1.hasStraightPreparableAtomStringExprs() || this.expr2.hasStraightPreparableAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		atomStringExprs.addAll(this.expr1.getAtomStringExprs());
		atomStringExprs.addAll(this.expr2.getAtomStringExprs());
		return atomStringExprs;
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ArithmeticExpr))
			return false;

		ArithmeticExpr aritExpr = (ArithmeticExpr) object;

		return this.expr1.equals(aritExpr.expr1) 
				&& this.operator == aritExpr.operator
				&& this.expr2.equals(aritExpr.expr2);
	}

	@Override
	public Expression clone() {
		return new ArithmeticExpr(
				this.expr1.clone(), this.operator, this.expr2.clone());
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append(this.expr1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.operator.getAsciiName());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.expr2.toString());
		return stringRepresentation.toString();
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	private Expression handleArithmetic() {
		if (this.expr1 instanceof AtomExpr<?> && this.expr2 instanceof AtomExpr<?>
				&& ((AtomExpr<?>) this.expr1).isFinishedNumberType()
				&& ((AtomExpr<?>) this.expr2).isFinishedNumberType()) {
			return ((AtomExpr<?>) this.expr1).calc(((AtomExpr<?>) this.expr2), this.operator);
		} else
			return this;
	}
}
