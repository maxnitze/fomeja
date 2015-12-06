package de.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.fomeja.datatypes.PreField;
import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.exceptions.NotConvertibleException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class PrematureExpr extends Expression {
	/**
	 * COMMENT
	 */
	public PrematureExpr() {
		super();
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 */
	public PrematureExpr(Object object, List<PreField> preFields) {
		super(object, preFields);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean isBoolExpr() {
		return false;
	}

	@Override
	public BoolExpression toBoolExpr() {
		String message = "can not convert premature expression \"" + this.toString() + "\" to bool expression";
		Logger.getLogger(PrematureExpr.class).fatal(message);
		throw new NotConvertibleException(message);
	}

	@Override
	public boolean isUnfinished() {
		return true;
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		return false;
	}
}
