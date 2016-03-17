package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.AccessibleObject;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class PremAccessibleObjectExpr<T extends AccessibleObject> extends PrematureExpr {
	/** COMMENT */
	Expression expr;
	/** COMMENT */
	T accessibleObject;
	/** COMMENT */
	List<Expression> argExprs;

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * @param accessibleObject
	 * @param argExprs
	 */
	public PremAccessibleObjectExpr(Expression expr, T accessibleObject, List<Expression> argExprs) {
		this.expr = expr;
		this.accessibleObject = accessibleObject;
		this.argExprs = argExprs;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Expression getExpr() {
		return this.expr;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public T getAccessibleObject() {
		return this.accessibleObject;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<Expression> getArgumentExpressions() {
		return this.argExprs;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		for (Expression objectArgument : this.argExprs)
			if (objectArgument.matches(regex))
				return true;
		return this.expr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.expr.replaceAll(regex, replacement);

		for (Expression objectArgument : this.argExprs)
			objectArgument.replaceAll(regex, replacement);
	}

	@Override
	public PremAccessibleObjectExpr<T> substitude(Map<String, Expression> exprs) {
		this.expr = this.expr.substitude(exprs);

		List<Expression> substArgExprs = new ArrayList<Expression>();
		for (Expression argExpr : this.argExprs)
			substArgExprs.add(argExpr.substitude(exprs));
		this.argExprs = substArgExprs;

		return this;
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		requiredAtomExprs.addAll(this.expr.getRequiredAtomExprs(isRequired, compVars));
		for (Expression objectArgument : this.argExprs)
			requiredAtomExprs.addAll(objectArgument.getRequiredAtomExprs(isRequired, compVars));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		for (Expression objectArgument : this.argExprs)
			if (objectArgument.hasAtomVoidExprs())
				return true;
		return this.expr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		atomVoidExprs.addAll(this.expr.getAtomVoidExprs());
		for (Expression objectArgument : this.argExprs)
			atomVoidExprs.addAll(objectArgument.getAtomVoidExprs());
		return atomVoidExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		for (Expression expr : this.argExprs)
			if (expr.hasAtomStringExprs())
				return true;

		return this.expr.hasAtomStringExprs();
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		for (Expression expr : this.argExprs)
			if (expr.hasStraightPreparableAtomStringExprs())
				return true;

		return this.expr.hasStraightPreparableAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		atomStringExprs.addAll(this.expr.getAtomStringExprs());
		for (Expression objectArgument : this.argExprs)
			atomStringExprs.addAll(objectArgument.getAtomStringExprs());
		return atomStringExprs;
	}

	/** package private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	String getArgumentString() {
		StringBuilder argumentString = new StringBuilder();
		for (Expression argument : this.argExprs) {
			if (argumentString.length() > 0)
				argumentString.append(", ");
			argumentString.append(argument.toString());
		}

		return argumentString.toString();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	String getArgumentTypeString() {
		StringBuilder argumentTypeString = new StringBuilder();
		for (Expression argument : this.argExprs) {
			if (argumentTypeString.length() > 0)
				argumentTypeString.append(", ");
			argumentTypeString.append(argument.getResultType().getSimpleName().toString());
		}

		return argumentTypeString.toString();
	}
}
