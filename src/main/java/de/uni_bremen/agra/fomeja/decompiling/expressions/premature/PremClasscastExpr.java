package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PremClasscastExpr extends PrematureExpr {
	/** COMMENT */
	public static enum Keyword { i2f, i2d, f2d };

	/** COMMENT */
	private Expression expr;
	/** COMMENT */
	private final Keyword keyword;

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * @param keyword
	 */
	public PremClasscastExpr(Expression expr, Keyword keyword) {
		this.expr = expr;
		this.keyword = keyword;

		this.integrityCheck();
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Keyword getKeyword() {
		return this.keyword;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Expression getExpr() {
		return this.expr;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		switch (this.keyword) {
		case i2f:
			return Float.class;
		case i2d:
		case f2d:
			return Double.class;
		default:
			String message = "undefined casting \"" + this.keyword + "\" for expressions";
			Logger.getLogger(PremClasscastExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public boolean matches(String regex) {
		return this.expr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.expr.replaceAll(regex, replacement);
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		this.expr = this.expr.substitude(exprs);
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		this.expr = this.expr.evaluate(compVars);
		return this.handleCastings();
	}

	@Override
	public Expression simplify() {
		this.expr = this.expr.simplify();
		return this.handleCastings();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		return this.expr.getRequiredAtomExprs(isRequired, compVars);
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return this.expr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		return this.expr.getAtomVoidExprs();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.expr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.expr.getAtomStringExprs();
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremClasscastExpr))
			return false;

		PremClasscastExpr expr = (PremClasscastExpr) object;

		return this.expr.equals(expr.expr) && this.keyword.equals(expr.keyword);
	}

	@Override
	public Expression clone() {
		return new PremClasscastExpr(this.expr.clone(), this.keyword);
	}

	@Override
	public String toString() {
		return this.expr + "\" as \"" + (this.keyword == Keyword.i2f ? "float" : "double");
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 */
	private void integrityCheck() {
		switch (this.keyword) {
		case i2f:
			if (!ClassUtils.isIntegerType(this.expr.getResultType())) {
				String message = "unexpected type \"" + this.expr.getClass().getSimpleName() + "\" for special treatment \"i2f\"";
				Logger.getLogger(PremClasscastExpr.class).fatal(message);
				throw new IllegalArgumentException(message);
			} else
				break;
		case i2d:
			if (!ClassUtils.isIntegerType(this.expr.getResultType())) {
				String message = "unexpected type \"" + this.expr.getClass().getSimpleName() + "\" for special treatment \"i2d\"";
				Logger.getLogger(PremClasscastExpr.class).fatal(message);
				throw new IllegalArgumentException(message);
			} else
				break;
		case f2d:
			if (!ClassUtils.isFloatType(this.expr.getResultType())) {
				String message = "unexpected type \"" + this.expr.getClass().getSimpleName() + "\" for special treatment \"f2d\"";
				Logger.getLogger(PremClasscastExpr.class).fatal(message);
				throw new IllegalArgumentException(message);
			} else
				break;

		default:
			String message = "undefined special treatment \"" + this.keyword + "\" for constraint values";
			Logger.getLogger(PremClasscastExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	private Expression handleCastings() {
		switch (this.keyword) {
		case i2f:
			if (this.expr instanceof AtomIntegerExpr
					&& ((AtomIntegerExpr) this.expr).isFinishedType())
				return new AtomFloatExpr(((AtomIntegerExpr) this.expr).getValue().floatValue());
			else
				return this;
		case i2d:
			if (this.expr instanceof AtomIntegerExpr
					&& ((AtomIntegerExpr) this.expr).isFinishedType())
				return new AtomDoubleExpr(((AtomIntegerExpr) this.expr).getValue().doubleValue());
			else
				return this;
		case f2d:
			if (this.expr instanceof AtomFloatExpr
					&& ((AtomFloatExpr) this.expr).isFinishedType())
				return new AtomDoubleExpr(((AtomFloatExpr) this.expr).getValue().doubleValue());
			else
				return this;

		default:
			String message = "undefined special treatment \"" + this.keyword + "\" for constraint values";
			Logger.getLogger(PremClasscastExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}
}
