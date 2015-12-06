package de.agra.fomeja.decompiling.statements;

/* import */
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.premature.PremLoopStmtExpr;
import de.agra.fomeja.decompiling.misc.ComponentVariables;
import de.agra.fomeja.decompiling.statements.misc.State;
import de.agra.fomeja.exceptions.EvaluationException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class LoopStmt extends Statement {
	/** COMMENT */
	private BoolExpression condition;
	/** COMMENT */
	private StatementSeq body;

	/**
	 * COMMENT
	 * 
	 * @param condition
	 * @param body
	 */
	public LoopStmt(BoolExpression condition, StatementSeq body) {
		this.condition = condition;
		this.body = body;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public BoolExpression getCondition() {
		return this.condition;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public StatementSeq getBody() {
		return this.body;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.body.getResultType();
	}

	@Override
	public boolean matches(String regex) {
		return this.condition.matches(regex) || this.body.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.condition.replaceAll(regex, replacement);
		this.body.replaceAll(regex, replacement);
	}

	@Override
	public void substitude(Map<String, Expression> exprs) {
		this.condition = this.condition.substitude(exprs);
		this.body.substitude(exprs);
	}

	@Override
	public ReturnStmt evaluate(State outerState, ComponentVariables compVars) {
		BoolExpression curCond = this.condition.clone().substitude(outerState.getExprs()).evaluate(compVars);

		if (curCond instanceof AtomBoolExpr) {
			/* execute loop while condition is true */
			while(((AtomBoolExpr) curCond).getValue()) {
				FlowControlStmt flowControlStmt = this.body.clone().evaluate(outerState, compVars);
				if (flowControlStmt instanceof ReturnStmt && !(((ReturnStmt) flowControlStmt).getResultType().equals(Void.class))) {
					ReturnStmt returnStmt = (ReturnStmt) flowControlStmt;
					Map<String, Expression> substExprs = new HashMap<String, Expression>();
					for (AtomVoidExpr atomVoidExpr : returnStmt.getReturnExpr().getAtomVoidExprs())
						substExprs.put(atomVoidExpr.getName(), this.evaluate(atomVoidExpr.getState(), compVars).getReturnExpr());
					returnStmt.substitude(substExprs);
					return returnStmt;
				} else if (flowControlStmt instanceof BreakStmt)
					break;
	
				curCond = this.condition.clone().substitude(outerState.getExprs()).evaluate(compVars);
				if (!(curCond instanceof AtomBoolExpr)) {
					String message = "could not evaluate current loop condition \"" + this.condition + "\"";
					Logger.getLogger(LoopStmt.class).fatal(message);
					throw new EvaluationException(message);
				}
			}
	
			return new ReturnStmt(new AtomVoidExpr());
		} else
			return new ReturnStmt(new PremLoopStmtExpr(this, outerState, compVars));
	}

	@Override
	public void simplify() {
		this.condition = this.condition.simplify();
		this.body.simplify();
	}

	@Override
	public boolean isUnfinished() {
		return this.condition.isUnfinished() || this.body.isUnfinished();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		BoolExpression condition = this.condition.clone().substitude(state.getExprs()).evaluate(compVars);
		if (!(condition instanceof AtomBoolExpr) || ((AtomBoolExpr) condition).getValue()) {
			requiredAtomExprs.addAll(condition.getRequiredAtomExprs(true, compVars));
			requiredAtomExprs.addAll(this.body.getRequiredAtomExprs(isRequired, compVars, state));
		}
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.condition.hasAtomStringExprs() || this.body.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		atomStringExprs.addAll(this.condition.getAtomStringExprs());
		atomStringExprs.addAll(this.body.getAtomStringExprs());
		return atomStringExprs;
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof LoopStmt))
			return false;

		LoopStmt loopStmt = (LoopStmt) object;

		return this.condition.equals(loopStmt.condition)
				&& this.body.equals(loopStmt.body);
	}

	@Override
	public LoopStmt clone() {
		return new LoopStmt(this.condition.clone(), this.body.clone());
	}

	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("WHILE (");
		stringBuilder.append(this.condition.toString());
		stringBuilder.append(") {\n  ");
		stringBuilder.append(this.body.toString().replaceAll("\n", "\n  "));
		stringBuilder.append("\n}");
		return stringBuilder.toString();
	}
}
