package de.uni_bremen.agra.fomeja.decompiling.statements;

/* imports */
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.decompiling.statements.misc.State;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;
import de.uni_bremen.agra.fomeja.types.CompareOperator;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class IfThenElseStmt extends Statement {
	/** COMMENT */
	private List<CondStmtSeqPair> condStmtSeqPairs;
	/** COMMENT */
	private StatementSeq elseStmtSeq;

	/**
	 * COMMENT
	 * 
	 * @param elseStmtSeq COMMENT
	 */
	public IfThenElseStmt(StatementSeq elseStmtSeq) {
		this.condStmtSeqPairs = new ArrayList<CondStmtSeqPair>();
		this.elseStmtSeq = elseStmtSeq;
	}

	/**
	 * COMMENT
	 * 
	 * @param condition COMMENT
	 * @param thenStmtSeq COMMENT
	 * @param elseStmtSeq COMMENT
	 */
	public IfThenElseStmt(BoolExpression condition, StatementSeq thenStmtSeq, StatementSeq elseStmtSeq) {
		this.condStmtSeqPairs = new ArrayList<CondStmtSeqPair>();
		this.condStmtSeqPairs.add(new CondStmtSeqPair(condition, thenStmtSeq));
		this.elseStmtSeq = elseStmtSeq;
	}

	/* getter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public List<CondStmtSeqPair> getCondStmtSeqPairs() {
		return this.condStmtSeqPairs;
	}

	/**
	 * COMMENT
	 * 
	 * @param condition COMMENT
	 * @param stmtSeq COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean add(BoolExpression condition, StatementSeq stmtSeq) {
		return this.condStmtSeqPairs.add(new CondStmtSeqPair(condition, stmtSeq));
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public StatementSeq getElseStmt() {
		return this.elseStmtSeq;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		Class<?> resultType = Void.class;
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs)
			resultType = ClassUtils.getMostCommonTypeVoidExcluded(resultType, condStmtSeqPair.stmtSeq.getResultType());
		return ClassUtils.getMostCommonTypeVoidExcluded(resultType, this.elseStmtSeq.getResultType());
	}

	@Override
	public boolean matches(String regex) {
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs)
			if (condStmtSeqPair.condition.matches(regex) || condStmtSeqPair.stmtSeq.matches(regex))
				return true;
		return this.elseStmtSeq.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			condStmtSeqPair.condition.replaceAll(regex, replacement);
			condStmtSeqPair.stmtSeq.replaceAll(regex, replacement);
		}
		this.elseStmtSeq.replaceAll(regex, replacement);
	}

	@Override
	public void substitude(Map<String, Expression> exprs) {
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			condStmtSeqPair.condition.substitude(exprs);
			condStmtSeqPair.stmtSeq.substitude(exprs);
		}
		this.elseStmtSeq.substitude(exprs);
	}

	@Override
	public FlowControlStmt evaluate(State outerState, ComponentVariables compVars) {
		boolean allAtomar = true;
		boolean allBool = true;
		List<CondReturnStmtPair> evaluatedcondReturnStmtPairs = new ArrayList<CondReturnStmtPair>();
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			BoolExpression evaluatedCondition = condStmtSeqPair.condition.clone().substitude(outerState.getExprs()).evaluate(compVars);
			if (allAtomar && evaluatedCondition instanceof AtomBoolExpr) {
				if (((AtomBoolExpr) evaluatedCondition).getValue())
					return condStmtSeqPair.stmtSeq.evaluate(outerState, compVars);
			} else {
				if (allAtomar)
					allAtomar = false;
				/* skip unreachable statement sequences */
				if (!(evaluatedCondition instanceof AtomBoolExpr) || ((AtomBoolExpr) evaluatedCondition).getValue()) {
					/** TODO State Changes
					 * when followed by other code the additions from the
					 * single if-then-else statements sequences need to be
					 * included in the state ==> copy for each statement (that
					 * changes the state in a different way)
					 * ----- ----- ----- ----- ----- ----- ----- ----- ----- */
					FlowControlStmt cFCStmt = condStmtSeqPair.stmtSeq.evaluate(outerState.clone(), compVars);
					if (cFCStmt instanceof ReturnStmt) {
						if (allBool && !((ReturnStmt) cFCStmt).getReturnExpr().isBoolExpr())
							allBool = false;
						evaluatedcondReturnStmtPairs.add(new CondReturnStmtPair(evaluatedCondition, (ReturnStmt) cFCStmt));
					} else {
						String message = "if-then-else statement with non-atomar conditions needs to return return statement but returns \"" + cFCStmt + "\"";
						Logger.getLogger(IfThenElseStmt.class).fatal(message);
						throw new EvaluationException(message);
					}
				}
			}
		}

		if (allAtomar || evaluatedcondReturnStmtPairs.isEmpty())
			return this.elseStmtSeq.evaluate(outerState, compVars);
		else {
			/** TODO State Changes (like before) */
			FlowControlStmt elseFCStmt = this.elseStmtSeq.evaluate(outerState.clone(), compVars);
			if (elseFCStmt instanceof ReturnStmt) {
				if (allBool && ((ReturnStmt) elseFCStmt).getReturnExpr().isBoolExpr()) {
					BoolExpression elseBoolExpr;
					if (((ReturnStmt) elseFCStmt).getReturnExpr() instanceof AtomBoolExpr)
						elseBoolExpr = (AtomBoolExpr) ((ReturnStmt) elseFCStmt).getReturnExpr();
					else
						elseBoolExpr = new CompareExpr(((ReturnStmt) elseFCStmt).getReturnExpr(), CompareOperator.EQUAL, new AtomIntegerExpr(1));
					BoolIfThenElseExpr boolIfThenElseExpr = new BoolIfThenElseExpr(elseBoolExpr);
					for (CondReturnStmtPair condReturnStmtPair : evaluatedcondReturnStmtPairs) {
						if (condReturnStmtPair.returnStmt.getReturnExpr() instanceof AtomBoolExpr)
							boolIfThenElseExpr.add(condReturnStmtPair.condition, (AtomBoolExpr) condReturnStmtPair.returnStmt.getReturnExpr());
						else
							boolIfThenElseExpr.add(condReturnStmtPair.condition, new CompareExpr(condReturnStmtPair.returnStmt.getReturnExpr(), CompareOperator.EQUAL, new AtomIntegerExpr(1)));
					}
					return new ReturnStmt(boolIfThenElseExpr);
				} else {
					IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(((ReturnStmt) elseFCStmt).getReturnExpr());
					for (CondReturnStmtPair condReturnStmtPair : evaluatedcondReturnStmtPairs)
						ifThenElseExpr.add(condReturnStmtPair.condition, condReturnStmtPair.returnStmt.getReturnExpr());
					return new ReturnStmt(ifThenElseExpr);
				}
			} else {
				String message = "if-then-else statement with non-atomar conditions needs to return return statement but returns \"" + elseFCStmt + "\"";
				Logger.getLogger(IfThenElseStmt.class).fatal(message);
				throw new EvaluationException(message);
			}
		}
	}

	@Override
	public void simplify() {
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs)
			condStmtSeqPair.simplify();
		this.elseStmtSeq.simplify();
	}

	@Override
	public boolean isUnfinished() {
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs)
			if (condStmtSeqPair.condition.isUnfinished() || condStmtSeqPair.stmtSeq.isUnfinished())
				return true;
		return this.elseStmtSeq.isUnfinished();
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state) {
		/** TODO State Changes (like before) */
		boolean isFinished = false;
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();

		/** check for fully evaluatable condition */
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			BoolExpression evalCond = condStmtSeqPair.condition.clone().substitude(state.getExprs()).evaluate(compVars);
			if (evalCond instanceof AtomBoolExpr && ((AtomBoolExpr) evalCond).getValue()) {
				requiredAtomExprs.addAll(evalCond.getRequiredAtomExprs(isRequired, compVars.clone()));
				requiredAtomExprs.addAll(condStmtSeqPair.stmtSeq.getRequiredAtomExprs(isRequired, compVars.clone(), state.clone()));
				isFinished = true;
				break;
			}
		}
		if (isFinished)
			return requiredAtomExprs;

		/** get required atomar expressions from all non-false condition pairs */
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			BoolExpression evalCond = condStmtSeqPair.condition.clone().substitude(state.getExprs()).evaluate(compVars);
			if (!(evalCond instanceof AtomBoolExpr) || ((AtomBoolExpr) evalCond).getValue()) {
				requiredAtomExprs.addAll(evalCond.getRequiredAtomExprs(isRequired, compVars.clone()));
				requiredAtomExprs.addAll(condStmtSeqPair.stmtSeq.getRequiredAtomExprs(isRequired, compVars.clone(), state.clone()));
			}
		}
		requiredAtomExprs.addAll(this.elseStmtSeq.getRequiredAtomExprs(isRequired, compVars.clone(), state.clone()));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs)
			if (condStmtSeqPair.hasAtomStringExprs())
				return true;
		return this.elseStmtSeq.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			atomStringExprs.addAll(condStmtSeqPair.condition.getAtomStringExprs());
			atomStringExprs.addAll(condStmtSeqPair.stmtSeq.getAtomStringExprs());
		}
		atomStringExprs.addAll(this.elseStmtSeq.getAtomStringExprs());
		return atomStringExprs;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof IfThenElseStmt))
			return false;

		IfThenElseStmt ifThenElseStmt = (IfThenElseStmt) object;

		if (this.condStmtSeqPairs.size() != ifThenElseStmt.condStmtSeqPairs.size())
			return false;

		for (int i=0; i<this.condStmtSeqPairs.size(); i++)
			if (!this.condStmtSeqPairs.get(i).equals(ifThenElseStmt.condStmtSeqPairs.get(i)))
				return false;

		return this.elseStmtSeq.equals(ifThenElseStmt.elseStmtSeq);
	}

	@Override
	public IfThenElseStmt clone() {
		IfThenElseStmt ifThenElseStmt = new IfThenElseStmt(this.elseStmtSeq.clone());
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs)
			ifThenElseStmt.add(condStmtSeqPair.condition.clone(), condStmtSeqPair.stmtSeq.clone());
		return ifThenElseStmt;
	}

	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder();
		for (CondStmtSeqPair condStmtSeqPair : this.condStmtSeqPairs) {
			if (stringBuilder.length() == 0)
				stringBuilder.append("IF (");
			else
				stringBuilder.append("ELSE IF (");
			stringBuilder.append(condStmtSeqPair.condition.toString());
			stringBuilder.append(") {\n  ");
			stringBuilder.append(condStmtSeqPair.stmtSeq.toString().replaceAll("\n", "\n  "));
			stringBuilder.append("\n} ");
		}
		stringBuilder.append("ELSE {\n  ");
		stringBuilder.append(this.elseStmtSeq.toString().replaceAll("\n", "\n  "));
		stringBuilder.append("\n}");
		return stringBuilder.toString();
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class CondStmtSeqPair {
		/** COMMENT */
		private BoolExpression condition;
		/** COMMENT */
		private StatementSeq stmtSeq;

		/**
		 * COMMENT
		 * 
		 * @param condition COMMENT
		 * @param stmtSeq COMMENT
		 */
		public CondStmtSeqPair(BoolExpression condition, StatementSeq stmtSeq) {
			this.condition = condition;
			this.stmtSeq = stmtSeq;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public void simplify() {
			this.condition = this.condition.simplify();
			this.stmtSeq.simplify();
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public boolean hasAtomStringExprs() {
			return this.condition.hasAtomStringExprs() || this.stmtSeq.hasAtomStringExprs();
		}

		@Override
		public boolean equals(Object obj) {
			if (!(obj instanceof CondStmtSeqPair))
				return false;

			CondStmtSeqPair condStmtSeqPair = (CondStmtSeqPair) obj;

			return this.condition.equals(condStmtSeqPair.condition)
					&& this.stmtSeq.equals(condStmtSeqPair.stmtSeq);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class CondReturnStmtPair {
		/** COMMENT */
		private BoolExpression condition;
		/** COMMENT */
		private ReturnStmt returnStmt;

		/**
		 * COMMENT
		 * 
		 * @param condition COMMENT
		 * @param returnStmt COMMENT
		 */
		public CondReturnStmtPair(BoolExpression condition, ReturnStmt returnStmt) {
			this.condition = condition;
			this.returnStmt = returnStmt;
		}

		@Override
		public boolean equals(Object obj) {
			if (!(obj instanceof CondReturnStmtPair))
				return false;

			CondReturnStmtPair condReturnStmtPair = (CondReturnStmtPair) obj;

			return this.condition.equals(condReturnStmtPair.condition)
					&& this.returnStmt.equals(condReturnStmtPair.returnStmt);
		}
	}
}
