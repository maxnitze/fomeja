package de.uni_bremen.agra.fomeja.decompiling.expressions.misc;

/* imports */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class WildcardBoolExpr extends BoolExpression {
	/** COMMENT */
	private String name;

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public WildcardBoolExpr(String name) {
		this.name = name;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		return this.name;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		return this.name.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {}

	@Override
	public BoolExpression substitude(Map<String, Expression> exprs) {
		Expression substExpr = exprs.get(this.name);
		if (substExpr != null && substExpr.isBoolExpr())
			return substExpr.toBoolExpr();
		else
			return this;
	}

	@Override
	public WildcardBoolExpr evaluate(ComponentVariables compVars) {
		return this;
	}

	@Override
	public WildcardBoolExpr simplify() {
		return this;
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
	public Set<AtomStringExpr> getAtomStringExprs() {
		return new HashSet<AtomStringExpr>();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof WildcardBoolExpr))
			return false;

		return this.name.equals(((WildcardBoolExpr) object).name);
	}

	@Override
	public WildcardBoolExpr clone() {
		return new WildcardBoolExpr(this.name);
	}

	@Override
	public String toString() {
		return this.name;
	}
}
