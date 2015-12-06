package de.agra.fomeja.decompiling.expressions.bool;

/* imports */
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.fomeja.backends.parameterobjects.ParameterObject;
import de.agra.fomeja.backends.parameterobjects.RangedParameterObject;
import de.agra.fomeja.datatypes.PreFieldList;
import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.agra.fomeja.decompiling.misc.ComponentVariables;
import de.agra.fomeja.exceptions.EvaluationException;
import de.agra.fomeja.types.BooleanConnector;
import de.agra.fomeja.types.CompareOperator;
import de.agra.fomeja.utils.ExpressionUtils;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class CompareExpr extends BoolExpression {
	/** the first expression */
	private Expression expr1;
	/** the second expression */
	private Expression expr2;
	/** the constraint operator of the expressions */
	private CompareOperator operator;

	/**
	 * Constructor for a new compare expression.
	 * 
	 * @param expr1 the new first expression
	 * @param operator the new constraint operator of the values
	 * @param expr2 the new second expression
	 */
	public CompareExpr(Expression expr1, CompareOperator operator, Expression expr2) {
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
	public CompareOperator getOperator() {
		return this.operator;
	}

	/**
	 * COMMENT
	 */
	public void switchCompareOperator() {
		this.operator = this.operator.getOpposite();
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

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
	public CompareExpr substitude(Map<String, Expression> exprs) {
		this.expr1 = this.expr1.substitude(exprs);
		this.expr2 = this.expr2.substitude(exprs);

		return this;
	}

	@Override
	public BoolExpression evaluate(ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		requiredAtomExprs.addAll(this.expr1.getRequiredAtomExprs(false, compVars.clone()));
		requiredAtomExprs.addAll(this.expr2.getRequiredAtomExprs(false, compVars.clone()));

		if (!requiredAtomExprs.isEmpty()) {
			for (AtomExpr<?> unfinishedAtomExpr : requiredAtomExprs) {
				PreFieldList preFieldList = unfinishedAtomExpr.toPreFieldList();
				PreFieldList varHeadList = preFieldList.variableHead();
				if (!varHeadList.isEmpty()) {
					ParameterObject parameterObject = compVars.get(varHeadList.getName());
					if (parameterObject == null) {
						compVars.add(varHeadList);
						parameterObject = compVars.get(varHeadList.getName());
					}

					if (parameterObject instanceof RangedParameterObject) {
						RangedParameterObject rangedParameterObject = (RangedParameterObject) parameterObject;

						ConnectedBoolExpr connectedBoolExprSet = new ConnectedBoolExpr(BooleanConnector.OR);
						for (int j=0; j<rangedParameterObject.getRangeSize(); j++) {
							Object rangeObject = rangedParameterObject.getRangeElement(j);
							Map<String, Expression> substExprs = new HashMap<String, Expression>();
							substExprs.put(varHeadList.getName(), new AtomObjectExpr(rangeObject));
							if (varHeadList.size() < preFieldList.size())
								substExprs.put(preFieldList.getName(),
										new AtomObjectExpr(preFieldList.getFieldValue(varHeadList.size(), rangeObject)));

							connectedBoolExprSet.add(new ConnectedBoolExpr(
									BooleanConnector.AND,
									new CompareExpr(new AtomIntegerExpr(varHeadList.getName()), CompareOperator.EQUAL, new AtomIntegerExpr(j)),
									this.clone().substitude(substExprs).evaluate(compVars)));
						}

						return connectedBoolExprSet.evaluate(compVars);
					} else {
						String message;
						if (parameterObject != null)
							message = "cannot unfold unfinished loop statement for parameter object \"" + parameterObject + "\" of non-ranged type";
						else
							message = "no parameter object for required atomar expression \"" + varHeadList.getName() + "\"";
						Logger.getLogger(CompareExpr.class).fatal(message);
						throw new IllegalArgumentException(message);
					}
				} else {
					String message = "unfinished atomar expression \"" + unfinishedAtomExpr + "\" has no variable part (\"" + preFieldList.getName() + "\")";
					Logger.getLogger(CompareExpr.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			}

			String message = "required atom expressions of compare expression \"" + this + "\" could not get unfolded";
			Logger.getLogger(CompareExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		} else {
			this.expr1 = this.expr1.evaluate(compVars);
			this.expr2 = this.expr2.evaluate(compVars);
			return this.handleCompareOperation();
		}
	}

	@Override
	public BoolExpression simplify() {
		this.expr1 = this.expr1.simplify();
		this.expr2 = this.expr2.simplify();
		return this.handleCompareOperation();
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
		if (isRequired) {
			requiredAtomExprs.addAll(this.expr1.getRequiredAtomExprs(isRequired, compVars));
			requiredAtomExprs.addAll(this.expr2.getRequiredAtomExprs(isRequired, compVars));
		}
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
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		atomStringExprs.addAll(this.expr1.getAtomStringExprs());
		atomStringExprs.addAll(this.expr2.getAtomStringExprs());
		return atomStringExprs;
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof CompareExpr))
			return false;

		CompareExpr compareExpr = (CompareExpr) obj;

		return ((this.expr1.equals(compareExpr.expr1)
						&& this.expr2.equals(compareExpr.expr2)
						&& (this.operator == compareExpr.operator))
				|| (this.expr1.equals(compareExpr.expr2)
						&& this.expr2.equals(compareExpr.expr1)
						&& this.operator == compareExpr.operator.getSwapped()));
	}

	@Override
	public CompareExpr clone() {
		return new CompareExpr(
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
	private BoolExpression handleCompareOperation() {
		if (this.expr1 instanceof AtomExpr<?> && this.expr2 instanceof AtomExpr<?>)
			return ExpressionUtils.compareExpressions(
					(AtomExpr<?>) this.expr1, this.operator, (AtomExpr<?>) this.expr2);
		else if (this.expr1.isBoolExpr()) {
			if (this.expr2 instanceof AtomBoolExpr)
				return this.getMergedBoolExpr((AtomBoolExpr) this.expr2, this.operator.getSwapped(), this.expr1.toBoolExpr().simplify());
			else if (this.expr2 instanceof AtomIntegerExpr && ((AtomIntegerExpr) this.expr2).isFinishedType())
				return this.getMergedBoolExpr((AtomIntegerExpr) this.expr2, this.operator.getSwapped(), this.expr1.toBoolExpr().simplify());
			else
				return this;
		} else if (this.expr2.isBoolExpr()) {
			if (this.expr1 instanceof AtomBoolExpr)
				return this.getMergedBoolExpr((AtomBoolExpr) this.expr1, this.operator, this.expr2.toBoolExpr());
			else if (this.expr1 instanceof AtomIntegerExpr && ((AtomIntegerExpr) this.expr1).isFinishedType())
				return this.getMergedBoolExpr((AtomIntegerExpr) this.expr1, this.operator, this.expr2.toBoolExpr());
			else
				return this;
		} else
			return this;
	}

	/**
	 * COMMENT
	 * 
	 * @param atomIntegerExpr
	 * @param operator
	 * @param boolExpr
	 * 
	 * @return
	 */
	private BoolExpression getMergedBoolExpr(AtomIntegerExpr atomIntegerExpr, CompareOperator operator, BoolExpression boolExpr) {
		if (!atomIntegerExpr.isFinishedType()) {
			String message = "cannot merge bool expressions from non-finished atomar integer expression \"" + atomIntegerExpr + "\"";
			Logger.getLogger(CompareExpr.class).fatal(message);
			throw new EvaluationException(message);
		}

		return this.getMergedBoolExpr(new AtomBoolExpr(!atomIntegerExpr.getValue().equals(0)), operator, boolExpr);
	}

	/**
	 * COMMENT
	 * 
	 * @param atomBoolExpr
	 * @param operator
	 * @param boolExpr
	 * 
	 * @return
	 */
	private BoolExpression getMergedBoolExpr(AtomBoolExpr atomBoolExpr, CompareOperator operator, BoolExpression boolExpr) {
		String message;
		switch (operator) {
		case EQUAL:
			if (atomBoolExpr.getValue())
				return boolExpr;
			else
				return new NotExpr(boolExpr);
		case NOT_EQUAL:
			if (!atomBoolExpr.getValue())
				return boolExpr;
			else
				return new NotExpr(boolExpr);
		case GREATER:
		case GREATER_EQUAL:
		case LESS:
		case LESS_EQUAL:
			message = "cannot compare boolean expressions with operator \"" + operator.getAsciiName() + "\"";
			break;
		default:
			message = "compare operator \"" + operator.getAsciiName() + "\" is not known";
			break;
		}

		Logger.getLogger(CompareExpr.class).fatal(message);
		throw new EvaluationException(message);
	}
}
