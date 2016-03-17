package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.Array;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PremArraylengthExpr extends PrematureExpr {
	/** COMMENT */
	private Expression arrayExpr;

	/**
	 * COMMENT
	 * 
	 * @param arrayExpr COMMENT
	 */
	public PremArraylengthExpr(Expression arrayExpr) {
		this.arrayExpr = arrayExpr;

		if (!this.arrayExpr.getResultType().isArray()) {
			String message = "unexpected type \"" + this.arrayExpr.getClass().getSimpleName() + "\" as array";
			Logger.getLogger(PremArrayelementExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression getArrayExpr() {
		return this.arrayExpr;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.arrayExpr.getResultType().getComponentType();
	}

	@Override
	public boolean matches(String regex) {
		return this.arrayExpr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.arrayExpr.replaceAll(regex, replacement);
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		this.arrayExpr = this.arrayExpr.substitude(exprs);
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		this.arrayExpr = this.arrayExpr.evaluate(compVars);
		return this.handleArrayLength();
	}

	@Override
	public Expression simplify() {
		this.arrayExpr = this.arrayExpr.simplify();
		return this.handleArrayLength();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		return this.arrayExpr.getRequiredAtomExprs(isRequired, compVars);
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return this.arrayExpr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		return this.arrayExpr.getAtomVoidExprs();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.arrayExpr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.arrayExpr.getAtomStringExprs();
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremArraylengthExpr))
			return false;

		PremArraylengthExpr premExpr = (PremArraylengthExpr) object;

		return this.arrayExpr.equals(premExpr.arrayExpr);
	}

	@Override
	public PremArraylengthExpr clone() {
		return new PremArraylengthExpr(this.arrayExpr.clone());
	}

	@Override
	public String toString() {
		return "\"" + this.arrayExpr.toString() + "\".length";
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression handleArrayLength() {
		if (this.arrayExpr instanceof AtomObjectExpr
				&& ((AtomObjectExpr) this.arrayExpr).isFinishedType())
			return new AtomIntegerExpr(
					Array.getLength(((AtomObjectExpr) this.arrayExpr).getValue()));
		else if (this.arrayExpr instanceof AtomArrayExpr<?>)
			return new AtomIntegerExpr(((AtomArrayExpr<?>) this.arrayExpr).length());
		else
			return this;
	}
}
