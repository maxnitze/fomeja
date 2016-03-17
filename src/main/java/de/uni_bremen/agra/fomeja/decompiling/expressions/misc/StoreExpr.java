package de.uni_bremen.agra.fomeja.decompiling.expressions.misc;

/* imports */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.exceptions.NotConvertibleException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class StoreExpr extends Expression {
	/** COMMENT */
	private String name;
	/** COMMENT */
	private Class<?> resultType;

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 * @param resultType COMMENT
	 */
	public StoreExpr(String name, Class<?> resultType) {
		this.name = name;
		this.resultType = resultType;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getName() {
		return this.name;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.resultType;
	}

	@Override
	public boolean matches(String regex) {
		return this.name.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		if (exprs.get(this.name) != null)
			return exprs.get(this.name);
		else
			return this;
	}

	@Override
	public StoreExpr evaluate(ComponentVariables compVars) {
		return this;
	}

	@Override
	public StoreExpr simplify() {
		return this;
	}

	@Override
	public boolean isBoolExpr() {
		return false;
	}

	@Override
	public BoolExpression toBoolExpr() {
		String message = "can not convert store expression \"" + this.toString() + "\" to bool expression";
		Logger.getLogger(StoreExpr.class).fatal(message);
		throw new NotConvertibleException(message);
	}

	@Override
	public boolean isUnfinished() {
		return true;
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		return new HashSet<AtomExpr<?>>();
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
		return false;
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
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
		if (!(object instanceof StoreExpr))
			return false;

		return this.name.equals(((StoreExpr) object).name)
				&& this.resultType.equals(((StoreExpr) object).resultType);
	}

	@Override
	public Expression clone() {
		return new StoreExpr(this.name, this.resultType);
	}

	@Override
	public String toString() {
		return this.name;
	}
}
