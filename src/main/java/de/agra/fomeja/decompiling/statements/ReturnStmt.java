package de.agra.fomeja.decompiling.statements;

/* imports */
import java.util.Map;
import java.util.Set;
/* imports */
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.agra.fomeja.decompiling.expressions.Expression;

import de.agra.fomeja.decompiling.misc.ComponentVariables;
import de.agra.fomeja.decompiling.statements.misc.State;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ReturnStmt extends FlowControlStmt {
	/** COMMENT */
	private Expression returnExpr;

	/**
	 * COMMENT
	 * 
	 * @param returnExpr
	 */
	public ReturnStmt(Expression returnExpr) {
		this.returnExpr = returnExpr;
	}

	/** getter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Expression getReturnExpr() {
		return this.returnExpr;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.returnExpr.getResultType();
	}

	@Override
	public boolean matches(String regex) {
		return this.returnExpr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.returnExpr.replaceAll(regex, replacement);
	}

	@Override
	public void substitude(Map<String, Expression> exprs) {
		this.returnExpr = this.returnExpr.substitude(exprs);
	}

	@Override
	public ReturnStmt evaluate(State outerState, ComponentVariables compVars) {
		this.returnExpr = this.returnExpr.substitude(outerState.getExprs()).evaluate(compVars);
		if (this.returnExpr instanceof AtomVoidExpr)
			((AtomVoidExpr) this.returnExpr).setState(outerState);

		return this;
	}

	@Override
	public void simplify() {
		this.returnExpr.simplify();
	}

	@Override
	public boolean isUnfinished() {
		return this.returnExpr.isUnfinished();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state) {
		return this.returnExpr.clone().substitude(state.getExprs()).evaluate(compVars).getRequiredAtomExprs(isRequired, compVars);
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.returnExpr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.returnExpr.getAtomStringExprs();
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ReturnStmt))
			return false;

		return this.returnExpr.equals(((ReturnStmt) object).returnExpr);
	}

	@Override
	public ReturnStmt clone() {
		return new ReturnStmt(this.returnExpr.clone());
	}

	@Override
	public String toString() {
		if (!(this.returnExpr instanceof AtomVoidExpr))
			return "RETURN " + this.returnExpr.toString() + " (of type \"" + this.returnExpr.getResultType().getSimpleName() + "\")";
		else
			return ((AtomVoidExpr) this.returnExpr).getName();
	}
}
