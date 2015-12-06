package de.agra.fomeja.decompiling.expressions.atomar;

/* imports */
import java.lang.reflect.Field;

import org.apache.log4j.Logger;

import de.agra.fomeja.datatypes.PreFieldList;
import de.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.exceptions.NotConvertibleException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomIntegerExpr extends AtomExpr<Integer> {
	/**
	 * COMMENT
	 * 
	 * @param value
	 */
	public AtomIntegerExpr(Integer value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @parma opcode
	 * @param constantTableIndex
	 * @param preFields
	 */
	public AtomIntegerExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AtomIntegerExpr(String name) {
		super(name, true);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Integer.class;
	}

	@Override
	public boolean isBoolExpr() {
		return this.isFinishedType() && (this.getValue() == 0 || this.getValue() == 1);
	}

	@Override
	public BoolExpression toBoolExpr() {
		if (this.isBoolExpr())
			return this.getValue() == 0 ? new AtomBoolExpr(false) : new AtomBoolExpr(true);
		else {
			String message = "can not convert integer expression \"" + this.toString() + "\" to bool expression";
			Logger.getLogger(AtomIntegerExpr.class).fatal(message);
			throw new NotConvertibleException(message);
		}
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomIntegerExpr clone() {
		if (this.isFinishedType())
			return new AtomIntegerExpr(this.getValue());
		else if (this.getField() != null) {
			AtomIntegerExpr expr = new AtomIntegerExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		} else {
			AtomIntegerExpr expr = new AtomIntegerExpr(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
