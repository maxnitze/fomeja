package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

import java.lang.reflect.Array;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * COMMENT
 * 
 * @author Max Nitze
 *
 * @param <T> COMMENT
 */
public class AtomArrayExpr<T> extends AtomExpr<Expression[]> {
	/** COMMENT */
	private Class<T> type;

	/**
	 * COMMENT
	 * 
	 * @param type COMMENT
	 * @param size COMMENT
	 */
	public AtomArrayExpr(Class<T> type, int size) {
		super(new Expression[size]);
		this.type = type;
		for (int i=0; i<size; i++)
			this.getValue()[i] = new AtomObjectExpr(null);
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int length() {
		return this.getValue().length;
	}

	/**
	 * COMMENT
	 * 
	 * @param index COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression get(int index) {
		return this.getValue()[index];
	}

	/**
	 * COMMENT
	 * 
	 * @param index COMMENT
	 * @param expr COMMENT
	 */
	public void set(int index, Expression expr) {
		this.getValue()[index] = expr;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Class<T> getType() {
		return this.type;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Array.newInstance(this.type, 0).getClass();
	}

	@Override
	public boolean matches(String regex) {
		for (Expression value : this.getValue())
			if (value.matches(regex))
				return true;
		return false;
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		for (Expression value : this.getValue())
			value.replaceAll(regex, replacement);
	}

	@Override
	public AtomArrayExpr<T> substitude(Map<String, Expression> exprs) {
		for (int i=0; i<this.getValue().length; i++)
			this.getValue()[i] = this.getValue()[i].substitude(exprs);
		return this;
	}

	@Override
	public AtomArrayExpr<T> evaluate(ComponentVariables compVars) {
		for (int i=0; i<this.getValue().length; i++)
			this.getValue()[i] = this.getValue()[i].evaluate(compVars);
		return this;
	}

	@Override
	public AtomArrayExpr<T> simplify() {
		for (int i=0; i<this.getValue().length; i++)
			this.getValue()[i] = this.getValue()[i].simplify();
		return this;
	}

	@Override
	public boolean isUnfinished() {
		for (Expression value : this.getValue())
			if (value.isUnfinished())
				return true;
		return false;
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> atomExpr = new HashSet<AtomExpr<?>>();
		for (Expression value : this.getValue())
			atomExpr.addAll(value.getRequiredAtomExprs(isRequired, compVars));
		return atomExpr;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		for (Expression value : this.getValue())
			if (value.hasAtomVoidExprs())
				return true;
		return false;
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExpr = new HashSet<AtomVoidExpr>();
		for (Expression value : this.getValue())
			atomVoidExpr.addAll(value.getAtomVoidExprs());
		return atomVoidExpr;
	}

	@Override
	public boolean hasAtomStringExprs() {
		for (Expression value : this.getValue())
			if (value.hasAtomStringExprs())
				return true;
		return false;
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		for (Expression value : this.getValue())
			if (value.hasStraightPreparableAtomStringExprs())
				return true;
		return false;
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExpr = new HashSet<AtomStringExpr>();
		for (Expression value : this.getValue())
			atomStringExpr.addAll(value.getAtomStringExprs());
		return atomStringExpr;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AtomArrayExpr<?>))
			return false;

		AtomArrayExpr<?> arrayExpr = (AtomArrayExpr<?>) object;

		return super.equals(arrayExpr)
				&& this.type.equals(arrayExpr.type);
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(29, 3)
				.appendSuper(super.hashCode())
				.append(this.type)
				.toHashCode();
	}

	@Override
	public AtomArrayExpr<T> clone() {
		AtomArrayExpr<T> clonedArrayExpr = new AtomArrayExpr<T>(this.type, this.getValue().length);
		for (int i=0; i<this.getValue().length; i++)
			clonedArrayExpr.set(i, this.getValue()[i] != null ? this.getValue()[i].clone() : null);
		return clonedArrayExpr;
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder(this.type.getSimpleName()).append("[] { ");
		boolean first = true;
		for (Expression value : this.getValue()) {
			if (!first) {
				if (this.getValue().length > 3)
					stringRepresentation.append("\n ");
				stringRepresentation.append(", ");
			} else
				first = false;

			stringRepresentation.append(value != null ? value.toString() : "NULL");
		}

		return stringRepresentation
				.append(" }")
				.toString();
	}
}
