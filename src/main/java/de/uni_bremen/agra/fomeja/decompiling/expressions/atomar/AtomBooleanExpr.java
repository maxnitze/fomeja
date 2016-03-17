package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

/* imports */
import java.lang.reflect.Field;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomBooleanExpr extends AtomExpr<Boolean> {
	/**
	 * COMMENT
	 * 
	 * @param value
	 */
	public AtomBooleanExpr(Boolean value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param preFields
	 */
	public AtomBooleanExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AtomBooleanExpr(String name) {
		super(name, false);
	}

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
		if (this.isFinishedType())
			return new AtomBoolExpr(this.getValue());
		else
			return new CompareExpr(this, CompareOperator.EQUAL, new AtomBoolExpr(true));
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomBooleanExpr clone() {
		if (this.isFinishedType())
			return new AtomBooleanExpr(this.getValue());
		else if (this.getField() != null) {
			AtomBooleanExpr expr = new AtomBooleanExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		} else {
			AtomBooleanExpr expr = new AtomBooleanExpr(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
