package de.uni_bremen.agra.fomeja.decompiling.expressions.bool;

/* imports */
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
public class NotExpr extends BoolExpression {
	/** COMMENT */
	private BoolExpression boolExpr;

	/**
	 * COMMENT
	 * 
	 * @param boolExpr COMMENT
	 */
	public NotExpr(BoolExpression boolExpr) {
		this.boolExpr = boolExpr;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public BoolExpression getBoolExpr() {
		return this.boolExpr;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		return this.boolExpr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.boolExpr.replaceAll(regex, replacement);
	}

	@Override
	public BoolExpression substitude(Map<String, Expression> exprs) {
		this.boolExpr = this.boolExpr.substitude(exprs);
		return this;
	}

	@Override
	public BoolExpression evaluate(ComponentVariables compVars) {
		this.boolExpr = this.boolExpr.evaluate(compVars);

		if (this.boolExpr instanceof AtomBoolExpr)
			return new AtomBoolExpr(!((AtomBoolExpr) this.boolExpr).getValue());
		else
			return this;
	}

	@Override
	public BoolExpression simplify() {
		this.boolExpr = this.boolExpr.simplify();

		if (this.boolExpr instanceof AtomBoolExpr)
			return new AtomBoolExpr(!((AtomBoolExpr) this.boolExpr).getValue());
		else if (this.boolExpr instanceof CompareExpr) {
			((CompareExpr) this.boolExpr).switchCompareOperator();
			return this.boolExpr;
		} else
			return this;
	}

	@Override
	public boolean isUnfinished() {
		return this.boolExpr.isUnfinished();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		return this.boolExpr.getRequiredAtomExprs(isRequired, compVars);
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return this.boolExpr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		return this.boolExpr.getAtomVoidExprs();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.boolExpr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.boolExpr.getAtomStringExprs();
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof NotExpr))
			return false;

		return this.boolExpr.equals(((NotExpr) object).boolExpr);
	}

	@Override
	public BoolExpression clone() {
		return new NotExpr(this.boolExpr.clone());
	}

	@Override
	public String toString() {
		return "NOT (" + this.boolExpr.toString() + ")";
	}
}
