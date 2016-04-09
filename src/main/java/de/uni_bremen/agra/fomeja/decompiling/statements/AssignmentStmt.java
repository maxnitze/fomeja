package de.uni_bremen.agra.fomeja.decompiling.statements;

import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.decompiling.statements.misc.State;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AssignmentStmt extends Statement {
	/** COMMENT */
	private String name;
	/** COMMENT */
	private Expression value;

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 * @param value COMMENT
	 */
	public AssignmentStmt(String name, Expression value) {
		this.name = name;
		this.value = value;
	}

	/* getter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression getValue() {
		return this.value;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.value.getResultType();
	}

	@Override
	public boolean matches(String regex) {
		return this.name.matches(regex) || this.value.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		if (replacement instanceof String)
			this.name = this.name.replaceAll(regex, (String) replacement);
		this.value.replaceAll(regex, replacement);
	}

	@Override
	public void substitude(Map<String, Expression> exprs) {
		if (exprs.get(this.name) != null)
			this.value = exprs.get(this.name);
		this.value = this.value.substitude(exprs);
	}

	@Override
	public AssignmentStmt evaluate(State state, ComponentVariables compVars) {
		state.put(this.name, this.value.clone().substitude(state.getExprs()).evaluate(compVars));
		return this;
	}

	@Override
	public void simplify() {
		this.value = this.value.simplify();
	}

	@Override
	public boolean isUnfinished() {
		return this.value.isUnfinished();
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars, State state) {
		Expression expr = this.value.clone().substitude(state.getExprs()).evaluate(compVars);
		state.put(this.name, expr);
		return expr.getRequiredAtomExprs(isRequired, compVars);
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.value.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.value.getAtomStringExprs();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AssignmentStmt))
			return false;

		AssignmentStmt assignmentStmt = (AssignmentStmt) object;

		return this.name.equals(assignmentStmt.name)
				&& this.value.equals(assignmentStmt.value);
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 151)
				.append(this.name)
				.append(this.value)
				.toHashCode();
	}

	@Override
	public AssignmentStmt clone() {
		return new AssignmentStmt(this.name, this.value.clone());
	}

	@Override
	public String toString() {
		return this.name + " = " + this.value.toString();
	}
}
