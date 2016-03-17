package de.uni_bremen.agra.fomeja.decompiling.expressions.bool;

/* imports */
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class ConnectedBoolExpr extends BoolExpression {
	/** the boolean connector of both constraints */
	private final BooleanConnector connector;
	/** COMMENT */
	private List<BoolExpression> boolExprs;

	/**
	 * COMMENT
	 * 
	 * @param connector COMMENT
	 * @param boolExprs COMMENT
	 */
	public ConnectedBoolExpr(BooleanConnector connector, List<BoolExpression> boolExprs) {
		this.connector = connector;
		this.boolExprs = boolExprs;
	}

	/**
	 * COMMENT
	 * 
	 * @param connector COMMENT
	 * @param boolExprs COMMENT
	 */
	public ConnectedBoolExpr(BooleanConnector connector, BoolExpression... boolExprs) {
		this.connector = connector;
		this.boolExprs = new ArrayList<BoolExpression>(Arrays.asList(boolExprs));
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public List<BoolExpression> getBoolExprs() {
		return this.boolExprs;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public BooleanConnector getConnector() {
		return this.connector;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int size() {
		return this.boolExprs.size();
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean isEmpty() {
		return this.boolExprs.isEmpty();
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param boolExpr COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean add(BoolExpression boolExpr) {
		return this.boolExprs.add(boolExpr);
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExprs COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean addAll(Collection<BoolExpression> boolExprs) {
		return this.boolExprs.addAll(boolExprs);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		for (BoolExpression boolExpr : this.boolExprs)
			if (boolExpr.matches(regex))
				return true;
		return false;
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		for (BoolExpression boolExpr : this.boolExprs)
			boolExpr.replaceAll(regex, replacement);
	}

	@Override
	public BoolExpression substitude(Map<String, Expression> exprs) {
		for (int i=0; i<this.boolExprs.size(); i++)
			this.boolExprs.set(i, this.boolExprs.get(i).substitude(exprs));
		return this;
	}

	@Override
	public BoolExpression evaluate(ComponentVariables compVars) {
		if (this.boolExprs.isEmpty())
			return new AtomBoolExpr(true);

		List<BoolExpression> evalBoolExprs = new ArrayList<BoolExpression>();
		for (BoolExpression boolExpr : this.boolExprs) {
			BoolExpression evalBoolExpr = boolExpr.evaluate(compVars);
			if (evalBoolExpr instanceof ConnectedBoolExpr && ((ConnectedBoolExpr) evalBoolExpr).connector == this.connector)
				evalBoolExprs.addAll(((ConnectedBoolExpr) evalBoolExpr).boolExprs);
			else
				evalBoolExprs.add(evalBoolExpr);
		}
		this.boolExprs = evalBoolExprs;

		return this.handleConnectedExprSet();
	}

	@Override
	public BoolExpression simplify() {
		if (this.boolExprs.isEmpty())
			return new AtomBoolExpr(true);

		List<BoolExpression> simplifiedBoolExprs = new ArrayList<BoolExpression>();
		for (BoolExpression boolExpr : this.boolExprs) {
			BoolExpression simplifiedBoolExpr = boolExpr.simplify();
			if (simplifiedBoolExpr instanceof ConnectedBoolExpr && ((ConnectedBoolExpr) simplifiedBoolExpr).connector == this.connector)
				simplifiedBoolExprs.addAll(((ConnectedBoolExpr) simplifiedBoolExpr).boolExprs);
			else
				simplifiedBoolExprs.add(simplifiedBoolExpr);
		}
		this.boolExprs = simplifiedBoolExprs;

		return this.handleConnectedExprSet();
	}

	@Override
	public boolean isUnfinished() {
		for (BoolExpression boolExpr : this.boolExprs)
			if (boolExpr.isUnfinished())
				return true;
		return false;
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		for (BoolExpression boolExpr : this.boolExprs)
			requiredAtomExprs.addAll(boolExpr.getRequiredAtomExprs(isRequired, compVars));
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		for (BoolExpression boolExpr : this.boolExprs)
			if (boolExpr.hasAtomVoidExprs())
				return true;
		return false;
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		Set<AtomVoidExpr> atomVoidExprs = new HashSet<AtomVoidExpr>();
		for (BoolExpression boolExpr : this.boolExprs)
			atomVoidExprs.addAll(boolExpr.getAtomVoidExprs());
		return atomVoidExprs;
	}

	@Override
	public boolean hasAtomStringExprs() {
		for (BoolExpression boolExpr : this.boolExprs)
			if (boolExpr.hasAtomStringExprs())
				return true;
		return false;
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		Set<AtomStringExpr> atomStringExprs = new HashSet<AtomStringExpr>();
		for (BoolExpression boolExpr : this.boolExprs)
			atomStringExprs.addAll(boolExpr.getAtomStringExprs());
		return atomStringExprs;
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ConnectedBoolExpr))
			return false;

		ConnectedBoolExpr connectedBoolExprSet = (ConnectedBoolExpr) object;

		boolean constraintListsAreEqual = this.boolExprs.size() == connectedBoolExprSet.boolExprs.size();
		for (BoolExpression constraint : this.boolExprs)
			constraintListsAreEqual &= connectedBoolExprSet.boolExprs.contains(constraint);

		return constraintListsAreEqual && this.connector == connectedBoolExprSet.connector;
	}

	@Override
	public ConnectedBoolExpr clone() {
		List<BoolExpression> clonedBoolExprs = new LinkedList<BoolExpression>();
		for (BoolExpression boolExpr : this.boolExprs)
			clonedBoolExprs.add(boolExpr.clone());

		return new ConnectedBoolExpr(this.connector, clonedBoolExprs);
	}

	@Override
	public String toString() {
		if (!this.boolExprs.isEmpty()) {
			StringBuilder stringRepresentation = new StringBuilder();
			if (this.connector == BooleanConnector.OR)
				stringRepresentation.append("(");

			boolean first = true;
			for (BoolExpression boolExpr : this.boolExprs) {
				if (!first)
					stringRepresentation
							.append("\n  ")
							.append(this.connector.getCode())
							.append(" ");
				else
					first = false;
	
				if (!(boolExpr instanceof CompareExpr))
					stringRepresentation.append("(")
							.append(boolExpr.toString().replaceAll("\n", "\n  "))
							.append(")");
				else
					stringRepresentation
							.append(boolExpr.toString().replaceAll("\n", "\n  "));
			}

			if (this.connector == BooleanConnector.OR)
				stringRepresentation.append(")");
	
			return stringRepresentation.toString();
		} else
			return "TRUE";
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression handleConnectedExprSet() {
		List<BoolExpression> newBoolExprs = new ArrayList<BoolExpression>();
		for (BoolExpression boolExpr : this.boolExprs) {
			if (this.connector == BooleanConnector.AND) {
				if (boolExpr instanceof AtomBoolExpr) {
					if (!((AtomBoolExpr) boolExpr).getValue())
						return new AtomBoolExpr(false);
				} else
					newBoolExprs.add(boolExpr);
			} else if (this.connector == BooleanConnector.OR) {
				if (boolExpr instanceof AtomBoolExpr) {
					if (((AtomBoolExpr) boolExpr).getValue())
						return new AtomBoolExpr(true);
				} else
					newBoolExprs.add(boolExpr);
			} else {
				String message = "boolean connector \"" + this.connector.getCode() + "\" is not known";
				Logger.getLogger(ConnectedBoolExpr.class).fatal(message);
				throw new EvaluationException(message);
			}
		}

		if (newBoolExprs.isEmpty()) {
			if (this.connector == BooleanConnector.AND)
				return new AtomBoolExpr(true);
			else if(this.connector == BooleanConnector.OR)
				return new AtomBoolExpr(false);
			else {
				String message = "boolean connector \"" + this.connector.getCode() + "\" is not known";
				Logger.getLogger(ConnectedBoolExpr.class).fatal(message);
				throw new EvaluationException(message);
			}
		} else if (newBoolExprs.size() == 1)
			return newBoolExprs.get(0);
		else
			return new ConnectedBoolExpr(this.connector, newBoolExprs);
	}
}
