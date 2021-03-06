package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.decompiling.statements.FlowControlStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.ReturnStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.StatementSeq;
import de.uni_bremen.agra.fomeja.decompiling.statements.misc.State;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PremStmtSeqExpr extends PrematureExpr {
	/** COMMENT */
	private StatementSeq stmtSeq;

	/** COMMENT */
	private State substState;

	/**
	 * COMMENT
	 * 
	 * @param stmtSeq COMMENT
	 */
	public PremStmtSeqExpr(StatementSeq stmtSeq) {
		this.stmtSeq = stmtSeq;
		this.substState = new State();
	}

	/**
	 * COMMENT
	 * 
	 * @param stmtSeq COMMENT
	 * @param substState COMMENT
	 */
	private PremStmtSeqExpr(StatementSeq stmtSeq, State substState) {
		this.stmtSeq = stmtSeq;
		this.substState = substState;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.stmtSeq.getResultType();
	}

	@Override
	public boolean matches(String regex) {
		return this.stmtSeq.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.stmtSeq.replaceAll(regex, replacement);
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		this.stmtSeq.substitude(exprs);
		this.substState.substitude(exprs);
		for (Entry<String, Expression> expr : exprs.entrySet())
			if (!expr.getKey().startsWith("store"))
				this.substState.put(expr.getKey(), expr.getValue());
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		FlowControlStmt flowControlStmt = this.stmtSeq.evaluate(this.substState.clone(), compVars);
		if (flowControlStmt instanceof ReturnStmt) {
			return ((ReturnStmt) flowControlStmt).getReturnExpr();
		} else {
			String message = "statement sequence needs to return a return statement but returns \"" + flowControlStmt + "\" of type \"" + flowControlStmt.getClass().getSimpleName() + "\"";
			Logger.getLogger(PremStmtSeqExpr.class).fatal(message);
			throw new EvaluationException(message);
		}
	}

	@Override
	public Expression simplify() {
		this.stmtSeq.simplify();
		return this;
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		for (AtomExpr<?> requiredAtomExpr : this.stmtSeq.getRequiredAtomExprs(isRequired, compVars, this.substState))
			if (!this.substState.contains(requiredAtomExpr.getName()))
				requiredAtomExprs.add(requiredAtomExpr);
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return false;
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		return new HashSet<AtomVoidExpr>();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.stmtSeq.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.stmtSeq.getAtomStringExprs();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremStmtSeqExpr))
			return false;

		PremStmtSeqExpr premStmtSeqExpr = (PremStmtSeqExpr) object;

		return super.equals(premStmtSeqExpr)
				&& this.stmtSeq.equals(premStmtSeqExpr.stmtSeq);
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(47, 79)
				.appendSuper(super.hashCode())
				.append(this.stmtSeq)
				.toHashCode();
	}

	@Override
	public PremStmtSeqExpr clone() {
		return new PremStmtSeqExpr(this.stmtSeq.clone(), this.substState.clone());
	}

	@Override
	public String toString() {
		return "PREMATURE\n  " + this.stmtSeq.toString().replaceAll("\n", "\n  ");
	}
}
