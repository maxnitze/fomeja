package de.uni_bremen.agra.fomeja.decompiling.statements;

/* imports */
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
public abstract class Statement {
	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Class<?> getResultType();

	/**
	 * COMMENT
	 * 
	 * @param regex COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean matches(String regex);

	/**
	 * COMMENT
	 * 
	 * @param regex COMMENT
	 * @param replacement COMMENT
	 */
	public abstract void replaceAll(String regex, Object replacement);

	/**
	 * COMMENT
	 * 
	 * @param exprs COMMENT
	 */
	public abstract void substitude(Map<String, Expression> exprs);

	/**
	 * COMMENT
	 * 
	 * @param outerState COMMENT
	 * @param compVars COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Statement evaluate(State outerState, ComponentVariables compVars);

	/**
	 * COMMENT
	 */
	public abstract void simplify();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean isUnfinished();

	/* abstract atomar expr methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param isRequired COMMENT
	 * @param compVars COMMENT
	 * @param state COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state);

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean hasAtomStringExprs();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Set<AtomStringExpr> getAtomStringExprs();

	/* overridden abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param object COMMENT
	 * 
	 * @return COMMENT
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	@Override
	public abstract int hashCode();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	@Override
	public abstract Statement clone();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	@Override
	public abstract String toString();
}
