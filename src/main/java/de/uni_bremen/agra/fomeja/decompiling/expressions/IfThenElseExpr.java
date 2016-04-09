package de.uni_bremen.agra.fomeja.decompiling.expressions;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class IfThenElseExpr extends Expression implements Cloneable {
	/** COMMENT */
	private List<CondExprPair> condExprPairs;
	/** COMMENT */
	private Expression elseCaseExpr;

	/**
	 * COMMENT
	 * 
	 * @param elseCaseExpr COMMENT
	 */
	public IfThenElseExpr(Expression elseCaseExpr) {
		this.condExprPairs = new ArrayList<CondExprPair>();
		this.elseCaseExpr = elseCaseExpr;
	}

	/**
	 * COMMENT
	 * 
	 * @param condExpr COMMENT
	 * @param thenCaseExpr COMMENT
	 * @param elseCaseExpr COMMENT
	 */
	public IfThenElseExpr(BoolExpression condExpr, Expression thenCaseExpr, Expression elseCaseExpr) {
		this.condExprPairs = new ArrayList<CondExprPair>();
		this.condExprPairs.add(new CondExprPair(condExpr, thenCaseExpr));
		this.elseCaseExpr = elseCaseExpr;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public List<CondExprPair> getCondExprPairs() {
		return this.condExprPairs;
	}

	/**
	 * COMMENT
	 * 
	 * @param condition COMMENT
	 * @param expr COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean add(BoolExpression condition, Expression expr) {
		return this.condExprPairs.add(new CondExprPair(condition, expr));
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression getElseCaseExpr() {
		return this.elseCaseExpr;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		Class<?> resultType = Void.class;
		for (CondExprPair condExprPair : this.condExprPairs)
			resultType = ClassUtils.getMostCommonTypeVoidExcluded(resultType, condExprPair.expr.getResultType());
		return ClassUtils.getMostCommonTypeVoidExcluded(resultType, this.elseCaseExpr.getResultType());
	}

	@Override
	public boolean matches(String regex) {
		for (CondExprPair condExprPair : this.condExprPairs)
			if (condExprPair.condition.matches(regex) || condExprPair.expr.matches(regex))
				return true;
		return this.elseCaseExpr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		for (CondExprPair condExprPair : this.condExprPairs) {
			condExprPair.condition.replaceAll(regex, replacement);
			condExprPair.expr.replaceAll(regex, replacement);
		}
		this.elseCaseExpr.replaceAll(regex, replacement);
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		List<CondExprPair> substitutedCondExprPairs = new ArrayList<CondExprPair>();
		for (CondExprPair condExprPair : this.condExprPairs)
			substitutedCondExprPairs.add(new CondExprPair(condExprPair.condition.substitude(exprs), condExprPair.expr.substitude(exprs)));
		this.condExprPairs = substitutedCondExprPairs;
		this.elseCaseExpr = this.elseCaseExpr.substitude(exprs);
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		boolean allAtomar = true;
		List<CondExprPair> evaluatedCondExprPairs = new ArrayList<CondExprPair>();
		for (CondExprPair condExprPair : this.condExprPairs) {
			BoolExpression simplifiedCondition = condExprPair.condition.evaluate(compVars);
			if (allAtomar && simplifiedCondition instanceof AtomBoolExpr) {
				if (((AtomBoolExpr) simplifiedCondition).getValue())
					return condExprPair.expr.evaluate(compVars);
			} else {
				if (allAtomar)
					allAtomar = false;
				/* skip unreachable expressions */
				if (!(simplifiedCondition instanceof AtomBoolExpr && !((AtomBoolExpr) simplifiedCondition).getValue()))
					evaluatedCondExprPairs.add(new CondExprPair(simplifiedCondition, condExprPair.expr.evaluate(compVars)));
			}
		}

		if (evaluatedCondExprPairs.isEmpty())
			return this.elseCaseExpr.evaluate(compVars);
		else {
			this.condExprPairs = evaluatedCondExprPairs;
			this.elseCaseExpr = this.elseCaseExpr.evaluate(compVars);
			return this;
		}
	}

	@Override
	public Expression simplify() {
		boolean allAtomar = true;
		List<CondExprPair> evaluatedCondExprPairs = new ArrayList<CondExprPair>();
		for (CondExprPair condExprPair : this.condExprPairs) {
			BoolExpression simplifiedCondition = condExprPair.condition.simplify();
			if (allAtomar && simplifiedCondition instanceof AtomBoolExpr) {
				if (((AtomBoolExpr) simplifiedCondition).getValue())
					return condExprPair.expr.simplify();
			} else {
				if (allAtomar)
					allAtomar = false;
				/* skip unreachable expressions */
				if (!(simplifiedCondition instanceof AtomBoolExpr && !((AtomBoolExpr) simplifiedCondition).getValue()))
					evaluatedCondExprPairs.add(new CondExprPair(simplifiedCondition, condExprPair.expr.simplify()));
			}
		}

		if (evaluatedCondExprPairs.isEmpty())
			return this.elseCaseExpr.simplify();
		else {
			this.condExprPairs = evaluatedCondExprPairs;
			this.elseCaseExpr = this.elseCaseExpr.simplify();
			return this;
		}
	}

	@Override
	public boolean isBoolExpr() {
		for (CondExprPair condExprPair : this.condExprPairs)
			if (!condExprPair.expr.isBoolExpr())
				return false;
		return this.elseCaseExpr.isBoolExpr();
	}

	@Override
	public BoolExpression toBoolExpr() {
		BoolIfThenElseExpr boolIfThenElseExpr = new BoolIfThenElseExpr(this.elseCaseExpr.toBoolExpr());
		for (CondExprPair condExprPair : this.condExprPairs)
			boolIfThenElseExpr.add(condExprPair.condition, condExprPair.expr.toBoolExpr());
		return boolIfThenElseExpr;
	}

	@Override
	public boolean isUnfinished() {
		for (CondExprPair condExprPair : this.condExprPairs)
			if (condExprPair.condition.isUnfinished() || condExprPair.expr.isUnfinished())
				return true;
		return this.elseCaseExpr.isUnfinished();
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		for (CondExprPair condExprPair : this.condExprPairs) {
			requiredAtomExprs.addAll(condExprPair.condition.getRequiredAtomExprs(isRequired, compVars));
			requiredAtomExprs.addAll(condExprPair.expr.getRequiredAtomExprs(isRequired, compVars));
		}
		requiredAtomExprs.addAll(this.elseCaseExpr.getRequiredAtomExprs(isRequired, compVars));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		for (CondExprPair condExprPair : this.condExprPairs)
			if (condExprPair.expr.hasAtomVoidExprs())
				return true;
		return this.elseCaseExpr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		for (CondExprPair condExprPair : this.condExprPairs) {
			atomVoidExprs.addAll(condExprPair.condition.getAtomVoidExprs());
			atomVoidExprs.addAll(condExprPair.expr.getAtomVoidExprs());
		}
		atomVoidExprs.addAll(this.elseCaseExpr.getAtomVoidExprs());
		return atomVoidExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		for (CondExprPair condExprPair : this.condExprPairs)
			if (condExprPair.expr.hasAtomStringExprs())
				return true;
		return this.elseCaseExpr.hasAtomStringExprs();
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		for (CondExprPair condExprPair : this.condExprPairs)
			if (condExprPair.expr.hasStraightPreparableAtomStringExprs())
				return true;
		return this.elseCaseExpr.hasStraightPreparableAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		for (CondExprPair condExprPair : this.condExprPairs) {
			atomStringExprs.addAll(condExprPair.condition.getAtomStringExprs());
			atomStringExprs.addAll(condExprPair.expr.getAtomStringExprs());
		}
		atomStringExprs.addAll(this.elseCaseExpr.getAtomStringExprs());
		return atomStringExprs;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof IfThenElseExpr))
			return false;

		IfThenElseExpr ifThenElseExpr = (IfThenElseExpr) object;

		if (!super.equals(ifThenElseExpr))
			return false;

		if (this.condExprPairs.size() != ifThenElseExpr.condExprPairs.size())
			return false;

		for (int i=0; i<this.condExprPairs.size(); i++)
			if (!this.condExprPairs.get(i).equals(ifThenElseExpr.condExprPairs.get(i)))
				return false;

		return this.elseCaseExpr.equals(ifThenElseExpr.elseCaseExpr);
	}

	@Override
	public int hashCode() {
		HashCodeBuilder hashCodeBuilder = new HashCodeBuilder(83, 43)
				.appendSuper(super.hashCode());

		for (CondExprPair condExprPair : this.condExprPairs)
			hashCodeBuilder.append(condExprPair);
		hashCodeBuilder.append(this.elseCaseExpr);

		return hashCodeBuilder.toHashCode();
	}

	@Override
	public Expression clone() {
		IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(this.elseCaseExpr.clone());
		for (CondExprPair condExprPair : this.condExprPairs)
			ifThenElseExpr.add(condExprPair.condition.clone(), condExprPair.expr.clone());
		return ifThenElseExpr;
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		for (CondExprPair condExprPair : this.condExprPairs) {
			if (stringRepresentation.length() == 0)
				stringRepresentation.append("IF (");
			else
				stringRepresentation.append("\nELSE IF (");
			stringRepresentation.append(condExprPair.condition.toString());
			stringRepresentation.append(")\nTHEN (");
			stringRepresentation.append(condExprPair.expr.toString());
			stringRepresentation.append(") ");
		}
		stringRepresentation.append("\nELSE (");
		stringRepresentation.append(this.elseCaseExpr.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}

	/* inner classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	public static class CondExprPair {
		/** COMMENT */
		private BoolExpression condition;
		/** COMMENT */
		private Expression expr;

		/**
		 * COMMENT
		 * 
		 * @param condition COMMENT
		 * @param expr COMMENT
		 */
		public CondExprPair(BoolExpression condition, Expression expr) {
			this.condition = condition;
			this.expr = expr;
		}

		/* getter/setter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public BoolExpression getCondition() {
			return this.condition;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public Expression getExpr() {
			return this.expr;
		}

		/* overridden methods
		 * ----- ----- ----- ----- ----- */

		@Override
		public boolean equals(Object obj) {
			if (!(obj instanceof CondExprPair))
				return false;

			CondExprPair condBoolExprPair = (CondExprPair) obj;

			return this.condition.equals(condBoolExprPair.condition)
					&& this.expr.equals(condBoolExprPair.expr);
		}

		@Override
		public int hashCode() {
			return new HashCodeBuilder(127, 11)
					.append(this.condition)
					.append(this.expr)
					.toHashCode();
		}
	}
}
