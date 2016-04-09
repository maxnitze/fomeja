package de.uni_bremen.agra.fomeja.decompiling.expressions.bool;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AtomBoolExpr extends BoolExpression {
	/** the boolean value */
	private boolean value;

	/**
	 * COMMENT
	 * 
	 * @param value COMMENT
	 */
	public AtomBoolExpr(boolean value) {
		this.value = value;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean getValue() {
		return this.value;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		return false;
	}

	@Override
	public void replaceAll(String regex, Object replacement) {}

	@Override
	public AtomBoolExpr substitude(Map<String, Expression> expressions) {
		return this;
	}

	@Override
	public AtomBoolExpr evaluate(ComponentVariables compVars) {
		return this;
	}

	@Override
	public AtomBoolExpr simplify() {
		return this;
	}

	@Override
	public boolean isUnfinished() {
		return false;
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
		if (!(object instanceof AtomBoolExpr))
			return false;

		AtomBoolExpr atomBoolExpr = (AtomBoolExpr) object;
		return super.equals(atomBoolExpr)
				&& this.value == atomBoolExpr.value;
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 29)
				.appendSuper(super.hashCode())
				.append(this.value)
				.toHashCode();
	}

	@Override
	public AtomBoolExpr clone() {
		return new AtomBoolExpr(this.value);
	}

	@Override
	public String toString() {
		return this.value ? "true" : "false";
	}
}
