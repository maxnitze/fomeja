package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.statements.misc.State;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomVoidExpr extends AtomExpr<Void> implements Cloneable {
	/** COMMENT */
	private static int counter = 0;

	/** COMMENT */
	private State state;

	/**
	 * COMMENT
	 */
	public AtomVoidExpr() {
		super((Void) null);
		this.state = new State();
		this.setName("VOID_" + counter++);
	}

	/**
	 * COMMENT
	 * 
	 * @param state COMMENT
	 */
	private AtomVoidExpr(State state, String name) {
		super((Void) null);
		this.state = state;
		this.setName(name);
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public State getState() {
		return this.state;
	}

	/**
	 * COMMENT
	 * 
	 * @param state COMMENT
	 */
	public void setState(State state) {
		this.state = state;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Void.class;
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		if (exprs.get(this.getName()) != null)
			return exprs.get(this.getName());
		else
			return this;
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean hasAtomVoidExprs() {
		return true;
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		atomVoidExprs.add(this);
		return atomVoidExprs;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AtomVoidExpr))
			return false;

		AtomVoidExpr atomVoidExpr = (AtomVoidExpr) object;

		return super.equals(atomVoidExpr)
				&& this.getName().equals(atomVoidExpr.getName());
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(71, 89)
			.appendSuper(super.hashCode())
			.append(this.getName())
			.toHashCode();
	}

	@Override
	public AtomVoidExpr clone() {
		return new AtomVoidExpr(this.state.clone(), this.getName());
	}

	@Override
	public String toString() {
		return this.getName();
	}
}
