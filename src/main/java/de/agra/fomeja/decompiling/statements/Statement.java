package de.agra.fomeja.decompiling.statements;

/* imports */
import java.util.Map;
import java.util.Set;

import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.misc.ComponentVariables;
import de.agra.fomeja.decompiling.statements.misc.State;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class Statement {
	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract Class<?> getResultType();

	/**
	 * COMMENT
	 * 
	 * @param regex
	 * 
	 * @return
	 */
	public abstract boolean matches(String regex);

	/**
	 * COMMENT
	 * 
	 * @param regex
	 * @param replacement
	 */
	public abstract void replaceAll(String regex, Object replacement);

	/**
	 * COMMENT
	 * 
	 * @param exprs
	 * 
	 * @return
	 */
	public abstract void substitude(Map<String, Expression> exprs);

	/**
	 * COMMENT
	 * 
	 * @param outerState
	 * @param varExprs
	 * 
	 * @return
	 */
	public abstract Statement evaluate(State outerState, ComponentVariables compVars);

	/**
	 * COMMENT
	 */
	public abstract void simplify();

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract boolean isUnfinished();

	/** abstract atomar expr methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param isRequired
	 * @param compVars
	 * @param state
	 * 
	 * @return
	 */
	public abstract Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state);

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract boolean hasAtomStringExprs();

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract Set<AtomStringExpr> getAtomStringExprs();

	/** overridden abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param object
	 * 
	 * @return
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	@Override
	public abstract Statement clone();

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	@Override
	public abstract String toString();
}
