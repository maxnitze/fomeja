package de.uni_bremen.agra.fomeja.decompiling.expressions.bool;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class BoolIfThenElseExpr extends BoolExpression {
	/** COMMENT */
	private static enum AnalyzeType { evaluate, simplify };

	/** COMMENT */
	private List<CondBoolExprPair> condBoolExprPairs;
	/** COMMENT */
	private BoolExpression elseCaseExpr;

	/**
	 * COMMENT
	 * 
	 * @param elseCaseExpr COMMENT
	 */
	public BoolIfThenElseExpr(BoolExpression elseCaseExpr) {
		this.condBoolExprPairs = new ArrayList<CondBoolExprPair>();
		this.elseCaseExpr = elseCaseExpr;
	}

	/**
	 * COMMENT
	 * 
	 * @param condExpr COMMENT
	 * @param thenCaseExpr COMMENT
	 * @param elseCaseExpr COMMENT
	 */
	public BoolIfThenElseExpr(BoolExpression condExpr, BoolExpression thenCaseExpr, BoolExpression elseCaseExpr) {
		this.condBoolExprPairs = new ArrayList<CondBoolExprPair>();
		this.condBoolExprPairs.add(new CondBoolExprPair(condExpr, thenCaseExpr));
		this.elseCaseExpr = elseCaseExpr;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public List<CondBoolExprPair> getCondBoolExprPairs() {
		return this.condBoolExprPairs;
	}

	/**
	 * COMMENT
	 * 
	 * @param condition COMMENT
	 * @param boolExpr COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean add(BoolExpression condition, BoolExpression boolExpr) {
		return this.condBoolExprPairs.add(new CondBoolExprPair(condition, boolExpr));
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public BoolExpression getElseCaseExpr() {
		return this.elseCaseExpr;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs)
			if (condBoolExprPair.condition.matches(regex) || condBoolExprPair.boolExpr.matches(regex))
				return true;
		return this.elseCaseExpr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs) {
			condBoolExprPair.condition.replaceAll(regex, replacement);
			condBoolExprPair.boolExpr.replaceAll(regex, replacement);
		}
		this.elseCaseExpr.replaceAll(regex, replacement);
	}

	@Override
	public BoolExpression substitude(Map<String, Expression> exprs) {
		List<CondBoolExprPair> substitutedCondBoolExprPair = new ArrayList<CondBoolExprPair>();
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs)
			substitutedCondBoolExprPair.add(new CondBoolExprPair(condBoolExprPair.condition.substitude(exprs), condBoolExprPair.boolExpr.substitude(exprs)));
		this.condBoolExprPairs = substitutedCondBoolExprPair;
		this.elseCaseExpr = this.elseCaseExpr.substitude(exprs);
		return this;
	}

	@Override
	public BoolExpression evaluate(ComponentVariables compVars) {
		return this.handleByAnalyseType(AnalyzeType.evaluate, compVars);
	}

	@Override
	public BoolExpression simplify() {
		return this.handleByAnalyseType(AnalyzeType.simplify, null);
	}

	@Override
	public boolean isUnfinished() {
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs)
			if (condBoolExprPair.condition.isUnfinished() || condBoolExprPair.boolExpr.isUnfinished())
				return true;
		return this.elseCaseExpr.isUnfinished();
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs) {
			requiredAtomExprs.addAll(condBoolExprPair.condition.getRequiredAtomExprs(isRequired, compVars));
			requiredAtomExprs.addAll(condBoolExprPair.boolExpr.getRequiredAtomExprs(isRequired, compVars));
		}
		requiredAtomExprs.addAll(this.elseCaseExpr.getRequiredAtomExprs(isRequired, compVars));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs)
			if (condBoolExprPair.condition.hasAtomVoidExprs() || condBoolExprPair.boolExpr.hasAtomVoidExprs())
				return true;
		return this.elseCaseExpr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs) {
			atomVoidExprs.addAll(condBoolExprPair.condition.getAtomVoidExprs());
			atomVoidExprs.addAll(condBoolExprPair.boolExpr.getAtomVoidExprs());
		}
		atomVoidExprs.addAll(this.elseCaseExpr.getAtomVoidExprs());
		return atomVoidExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs)
			if (condBoolExprPair.condition.hasAtomStringExprs() || condBoolExprPair.boolExpr.hasAtomStringExprs())
				return true;
		return this.elseCaseExpr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs) {
			atomStringExprs.addAll(condBoolExprPair.condition.getAtomStringExprs());
			atomStringExprs.addAll(condBoolExprPair.boolExpr.getAtomStringExprs());
		}
		atomStringExprs.addAll(this.elseCaseExpr.getAtomStringExprs());
		return atomStringExprs;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof BoolIfThenElseExpr))
			return false;

		BoolIfThenElseExpr boolIfThenElseExpr = (BoolIfThenElseExpr) object;

		if (!super.equals(boolIfThenElseExpr))
			return false;

		if (this.condBoolExprPairs.size() != boolIfThenElseExpr.condBoolExprPairs.size())
			return false;

		for (int i=0; i<this.condBoolExprPairs.size(); i++)
			if (!this.condBoolExprPairs.get(i).equals(boolIfThenElseExpr.condBoolExprPairs.get(i)))
				return false;

		return this.elseCaseExpr.equals(boolIfThenElseExpr.elseCaseExpr);
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(79, 37)
				.appendSuper(super.hashCode())
				.append(this.condBoolExprPairs)
				.append(this.elseCaseExpr)
				.toHashCode();
	}

	@Override
	public BoolExpression clone() {
		BoolIfThenElseExpr boolIfThenElseExpr = new BoolIfThenElseExpr(this.elseCaseExpr.clone());
		for (CondBoolExprPair condExprPair : this.condBoolExprPairs)
			boolIfThenElseExpr.add(condExprPair.condition.clone(), condExprPair.boolExpr.clone());
		return boolIfThenElseExpr;
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs) {
			if (stringRepresentation.length() == 0)
				stringRepresentation.append("IF (");
			else
				stringRepresentation.append("\nELSE IF (");
			String conditionString = condBoolExprPair.condition.toString();
			if (conditionString.contains("\n")) {
				stringRepresentation.append("\n  ");
				stringRepresentation.append(conditionString.replaceAll("\n", "\n  "));
			} else
				stringRepresentation.append(conditionString);
			stringRepresentation.append(")\nTHEN (");
			String boolExprString = condBoolExprPair.boolExpr.toString();
			if (boolExprString.contains("\n")) {
				stringRepresentation.append("\n  ");
				stringRepresentation.append(boolExprString.replaceAll("\n", "\n  "));
			} else
				stringRepresentation.append(boolExprString);
			stringRepresentation.append(") ");
		}
		stringRepresentation.append("\nELSE (");
		String elseCaseExprString = this.elseCaseExpr.toString();
		if (elseCaseExprString.contains("\n")) {
			stringRepresentation.append("\n  ");
			stringRepresentation.append(elseCaseExprString.replaceAll("\n", "\n  "));
		} else
			stringRepresentation.append(elseCaseExprString);
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
	public static class CondBoolExprPair {
		/** COMMENT */
		private BoolExpression condition;
		/** COMMENT */
		private BoolExpression boolExpr;

		/**
		 * COMMENT
		 * 
		 * @param condition COMMENT
		 * @param boolExpr COMMENT
		 */
		public CondBoolExprPair(BoolExpression condition, BoolExpression boolExpr) {
			this.condition = condition;
			this.boolExpr = boolExpr;
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
		public BoolExpression getBoolExpr() {
			return this.boolExpr;
		}

		/* overridden methods
		 * ----- ----- ----- ----- ----- */

		@Override
		public boolean equals(Object obj) {
			if (!(obj instanceof CondBoolExprPair))
				return false;

			CondBoolExprPair condBoolExprPair = (CondBoolExprPair) obj;

			return this.condition.equals(condBoolExprPair.condition)
					&& this.boolExpr.equals(condBoolExprPair.boolExpr);
		}

		@Override
		public int hashCode() {
			return new HashCodeBuilder(19, 149)
					.append(this.condition)
					.append(this.boolExpr)
					.toHashCode();
		}
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param type COMMENT
	 * @param compVars COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression handleByAnalyseType(AnalyzeType type, ComponentVariables compVars) {
		boolean allAtomar = true;
		PrefixExpr prefixExpr = new PrefixExpr();
		List<CondBoolExprPair> handledCondBoolExprPairs = new ArrayList<CondBoolExprPair>();
		for (CondBoolExprPair condBoolExprPair : this.condBoolExprPairs) {
			BoolExpression handledCondition = this.handleByAnalyseType(type, condBoolExprPair.condition, compVars);
			if (allAtomar && handledCondition instanceof AtomBoolExpr) {
				if (((AtomBoolExpr) handledCondition).getValue())
					return this.handleByAnalyseType(type, condBoolExprPair.boolExpr, compVars);
			} else {
				BoolExpression handledBoolExpr = this.handleByAnalyseType(type, condBoolExprPair.boolExpr, compVars);
				if (handledBoolExpr instanceof AtomBoolExpr) {
					/** convert IF X THEN TRUE ELSE Y to X || Y */
					if (((AtomBoolExpr) handledBoolExpr).getValue())
						prefixExpr.addOrExpr(handledCondition);
					/** convert IF X THEN FALSE ELSE Y to NOT(X) && Y */
					else
						prefixExpr.addAndExpr(new NotExpr(handledCondition));
				} else {
					if (allAtomar)
						allAtomar = false;
					/* skip unreachable expressions */
					if (!(handledCondition instanceof AtomBoolExpr && !((AtomBoolExpr) handledCondition).getValue())) {
						if (prefixExpr.topExpr != null && !prefixExpr.topExpr.isEmpty()) {
							prefixExpr.topExpr.add(handledBoolExpr);
							handledCondBoolExprPairs.add(new CondBoolExprPair(handledCondition, this.handleByAnalyseType(type, prefixExpr.topExpr, compVars)));
							prefixExpr.clear();
						} else
							handledCondBoolExprPairs.add(new CondBoolExprPair(handledCondition, handledBoolExpr));
					}
				}
			}
		}

		if (handledCondBoolExprPairs.isEmpty()) {
			if (prefixExpr.topExpr != null && !prefixExpr.topExpr.isEmpty()) {
				prefixExpr.topExpr.add(this.elseCaseExpr);
				return this.handleByAnalyseType(type, prefixExpr.topExpr, compVars);
			} else
				return this.handleByAnalyseType(type, this.elseCaseExpr, compVars);
		} else {
			this.condBoolExprPairs = handledCondBoolExprPairs;
			if (prefixExpr.topExpr != null && !prefixExpr.topExpr.isEmpty()) {
				prefixExpr.topExpr.add(this.elseCaseExpr);
				this.elseCaseExpr = this.handleByAnalyseType(type, prefixExpr.topExpr, compVars);
			} else
				this.elseCaseExpr = this.handleByAnalyseType(type, this.elseCaseExpr, compVars);

			return this;
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param type COMMENT
	 * @param boolExpr COMMENT
	 * @param compVars COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression handleByAnalyseType(AnalyzeType type, BoolExpression boolExpr, ComponentVariables compVars) {
		switch (type) {
		case evaluate:
			return boolExpr.evaluate(compVars);
		case simplify:
			return boolExpr.simplify();
		default:
			String message = "analyze type \"" + type + "\" is unknown";
			Logger.getLogger(BoolIfThenElseExpr.class).fatal(message);
			throw new EvaluationException(message);
		}
	}

	/* inner classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class PrefixExpr {
		/** COMMENT */
		ConnectedBoolExpr topExpr;
		/** COMMENT */
		ConnectedBoolExpr andExpr;
		/** COMMENT */
		ConnectedBoolExpr orExpr;

		/**
		 * COMMENT
		 */
		public PrefixExpr() {
			this.clear();
		}

		/* class methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param boolExpr COMMENT
		 */
		public void addAndExpr(BoolExpression boolExpr) {
			if (this.andExpr == null)
				this.andExpr = new ConnectedBoolExpr(BooleanConnector.AND);

			if (this.topExpr == null)
				this.topExpr = this.andExpr;
			else if (this.orExpr != null) {
				this.orExpr.add(this.andExpr);
				this.orExpr = null;
			}

			this.andExpr.add(boolExpr);
		}

		/**
		 * COMMENT
		 * 
		 * @param boolExpr COMMENT
		 */
		public void addOrExpr(BoolExpression boolExpr) {
			if (this.orExpr == null)
				this.orExpr = new ConnectedBoolExpr(BooleanConnector.OR);

			if (this.topExpr == null)
				this.topExpr = this.orExpr;
			else if (this.andExpr != null) {
				this.andExpr.add(this.orExpr);
				this.andExpr = null;
			}

			this.orExpr.add(boolExpr);
		}

		/**
		 * COMMENT
		 */
		public void clear() {
			this.topExpr = null;
			this.andExpr = null;
			this.orExpr = null;
		}
	}
}
