package de.uni_bremen.agra.fomeja.decompiling.expressions.bool;

import java.util.Map;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;

/**
 * BoolExpression is an abstract class for all types of boolean expressions.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class BoolExpression extends Expression {
	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Boolean.class;
	}

	@Override
	public boolean isBoolExpr() {
		return true;
	}

	@Override
	public BoolExpression toBoolExpr() {
		return this;
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		return false;
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public abstract BoolExpression substitude(Map<String, Expression> exprs);

	@Override
	public abstract BoolExpression evaluate(ComponentVariables compVars);

	@Override
	public abstract BoolExpression simplify();

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public abstract BoolExpression clone();
}
