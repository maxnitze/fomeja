package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.Array;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PremArrayelementExpr extends PrematureExpr {
	/** COMMENT */
	private Expression arrayExpr;
	/** COMMENT */
	private Expression indexExpr;

	/**
	 * COMMENT
	 * 
	 * @param arrayExpr COMMENT
	 * @param indexExpr COMMENT
	 */
	public PremArrayelementExpr(Expression arrayExpr, Expression indexExpr) {
		this.arrayExpr = arrayExpr;
		this.indexExpr = indexExpr;

		if (!this.arrayExpr.getResultType().isArray()) {
			String message = "unexpected type \"" + this.arrayExpr.getClass().getSimpleName() + "\" as array";
			Logger.getLogger(PremArrayelementExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		} else if (!ClassUtils.isIntegerType(this.indexExpr.getResultType())) {
			String message = "unexpected type \"" + this.indexExpr.getClass().getSimpleName() + "\" as array index";
			Logger.getLogger(PremArrayelementExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression getArrayExpr() {
		return this.arrayExpr;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression getIndexExpr() {
		return this.indexExpr;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.arrayExpr.getResultType().getComponentType();
	}

	@Override
	public boolean matches(String regex) {
		return this.arrayExpr.matches(regex) || this.indexExpr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.arrayExpr.replaceAll(regex, replacement);
		this.indexExpr.replaceAll(regex, replacement);
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		this.arrayExpr = this.arrayExpr.substitude(exprs);
		this.indexExpr = this.indexExpr.substitude(exprs);
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		this.arrayExpr = this.arrayExpr.evaluate(compVars);
		this.indexExpr = this.indexExpr.evaluate(compVars);
		return this.handleArrayelement();
	}

	@Override
	public Expression simplify() {
		this.arrayExpr = this.arrayExpr.simplify();
		this.indexExpr = this.indexExpr.simplify();
		return this.handleArrayelement();
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		requiredAtomExprs.addAll(this.arrayExpr.getRequiredAtomExprs(isRequired, compVars));
		requiredAtomExprs.addAll(this.indexExpr.getRequiredAtomExprs(isRequired, compVars));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return this.arrayExpr.hasAtomVoidExprs() || this.indexExpr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		atomVoidExprs.addAll(this.arrayExpr.getAtomVoidExprs());
		atomVoidExprs.addAll(this.indexExpr.getAtomVoidExprs());
		return atomVoidExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.arrayExpr.hasAtomStringExprs() || this.indexExpr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		atomStringExprs.addAll(this.arrayExpr.getAtomStringExprs());
		atomStringExprs.addAll(this.indexExpr.getAtomStringExprs());
		return atomStringExprs;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremArrayelementExpr))
			return false;

		PremArrayelementExpr premArrayelementExpr = (PremArrayelementExpr) object;

		return super.equals(premArrayelementExpr)
				&& this.arrayExpr.equals(premArrayelementExpr.arrayExpr)
				&& this.indexExpr.equals(premArrayelementExpr.indexExpr);
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(191, 101)
				.appendSuper(super.hashCode())
				.append(this.arrayExpr)
				.append(this.indexExpr)
				.toHashCode();
	}

	@Override
	public PremArrayelementExpr clone() {
		return new PremArrayelementExpr(this.arrayExpr.clone(), this.indexExpr.clone());
	}

	@Override
	public String toString() {
		return this.arrayExpr.toString() + "[" + this.indexExpr.toString() + "]";
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression handleArrayelement() {
		if (this.arrayExpr instanceof AtomObjectExpr
				&& ((AtomObjectExpr) this.arrayExpr).isFinishedType()
				&& this.indexExpr instanceof AtomIntegerExpr
				&& ((AtomIntegerExpr) this.indexExpr).isFinishedType())
			return this.getAtomExprFromValue(
					Array.get(
							((AtomObjectExpr) this.arrayExpr).getValue(),
							((AtomIntegerExpr) this.indexExpr).getValue()));
		else if (this.arrayExpr instanceof AtomArrayExpr<?>
				&& this.indexExpr instanceof AtomIntegerExpr
				&& ((AtomIntegerExpr) this.indexExpr).isFinishedType())
			return ((AtomArrayExpr<?>) this.arrayExpr).get(((AtomIntegerExpr) this.indexExpr).getValue());
		else
			return this;
	}

	/**
	 * COMMENT
	 * 
	 * @param object COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomExpr<?> getAtomExprFromValue(Object object) {
		if (ClassUtils.isBooleanType(object.getClass()))
			return new AtomIntegerExpr(((Boolean) object).equals(true) ? 1 : 0);
		else if (ClassUtils.isIntegerType(object.getClass()))
			return new AtomIntegerExpr((Integer) object);
		else if (ClassUtils.isFloatType(object.getClass()))
			return new AtomFloatExpr((Float) object);
		else if (ClassUtils.isDoubleType(object.getClass()))
			return new AtomDoubleExpr((Double) object);
		else if (ClassUtils.isLongType(object.getClass()))
			return new AtomIntegerExpr(((Long) object).intValue());
		else if (ClassUtils.isShortType(object.getClass()))
			return new AtomIntegerExpr(((Short) object).intValue());
		else if (ClassUtils.isCharType(object.getClass()))
			throw new RuntimeException("get expression from char value not implemented yet"); // TODO implement
		else if (ClassUtils.isByteType(object.getClass()))
			throw new RuntimeException("get expression from byte value not implemented yet"); // TODO implement
		else
			return new AtomObjectExpr(object);
	}
}
