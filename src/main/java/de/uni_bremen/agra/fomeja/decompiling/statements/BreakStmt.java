package de.uni_bremen.agra.fomeja.decompiling.statements;

/* imports */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.decompiling.statements.misc.State;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class BreakStmt extends FlowControlStmt {
	@Override
	public Class<Void> getResultType() {
		return Void.class;
	}

	@Override
	public boolean matches(String regex) {
		return false;
	}

	@Override
	public void replaceAll(String regex, Object replacement) {}

	@Override
	public void substitude(Map<String, Expression> exprs) {}

	@Override
	public BreakStmt evaluate(State outerState, ComponentVariables compVars) {
		return this;
	}

	@Override
	public void simplify() {}

	@Override
	public boolean isUnfinished() {
		return false;
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state) {
		return new HashSet<AtomExpr<?>>();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return false;
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return new HashSet<AtomStringExpr>();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (object instanceof BreakStmt)
			return true;
		else
			return false;
	}

	@Override
	public Statement clone() {
		return new BreakStmt();
	}

	@Override
	public String toString() {
		return "BREAK";
	}
}
