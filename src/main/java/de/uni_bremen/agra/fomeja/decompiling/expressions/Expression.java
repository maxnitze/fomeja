package de.uni_bremen.agra.fomeja.decompiling.expressions;

/* imports */
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_bremen.agra.fomeja.datatypes.PreField;
import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * AbstractConstraint is an abstract class for all types of constraint values.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Expression {
	/** COMMENT */
	private PreFieldList preFields;

	/**
	 * COMMENT
	 */
	public Expression() {
		this.preFields = new PreFieldList(null);
	}

	/**
	 * COMMENT
	 * 
	 * @param object COMMENT
	 */
	public Expression(Object object) {
		this.preFields = new PreFieldList(object);
	}

	/**
	 * COMMENT
	 * 
	 * @param object COMMENT
	 * @param preFields COMMENT
	 */
	public Expression(Object object, List<PreField> preFields) {
		this.preFields = new PreFieldList(object, preFields);
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public PreFieldList getPreFieldList() {
		return this.preFields;
	}

	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Class<?> getResultType();

	/**
	 * matches checks if this abstract constraint value matches the given
	 *  regular expression {@code regex}.
	 * 
	 * @param regex the regular expression
	 * 
	 * @return {@code true} if this abstract constraint value matches the given
	 *  regular expression {@code regex}, {@code false} otherwise
	 */
	public abstract boolean matches(String regex);

	/**
	 * replaceAll replaces all occurrences of the given regular expression
	 * 	{@code regex} with the given {@code replacement}.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the replacement
	 */
	public abstract void replaceAll(String regex, Object replacement);

	/**
	 * COMMENT
	 * 
	 * @param exprs COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Expression substitude(Map<String, Expression> exprs);

	/**
	 * evaluate evaluates the abstract constraint value.
	 * 
	 * @param compVars COMMENT
	 * 
	 * @return the evaluated expression
	 */
	public abstract Expression evaluate(ComponentVariables compVars);

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Expression simplify();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean isBoolExpr();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract BoolExpression toBoolExpr();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean isUnfinished();

	/** abstract atomar expr methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param isRequired COMMENT
	 * @param compVars COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars);

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean hasAtomVoidExprs();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Set<AtomVoidExpr> getAtomVoidExprs();

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
	public abstract boolean hasStraightPreparableAtomStringExprs();

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Set<AtomStringExpr> getAtomStringExprs();

	/** overridden abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * equals checks if this abstract constraint value and the given object are
	 *  equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object matches this abstract
	 *  constraint value, {@code false} otherwise
	 */
	@Override
	public abstract boolean equals(Object object);

	/**
	 * clone returns a copy of this abstract constraint value.
	 * 
	 * @return a copy of this abstract constraint value
	 */
	@Override
	public abstract Expression clone();

	/**
	 * toString returns the string representation of this abstract constraint
	 *  value.
	 * 
	 * @return the string representation of this abstract constraint value
	 */
	@Override
	public abstract String toString();
}
