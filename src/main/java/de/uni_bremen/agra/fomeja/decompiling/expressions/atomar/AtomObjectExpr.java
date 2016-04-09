package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

import java.lang.reflect.Field;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomObjectExpr extends AtomExpr<Object> {
	/**
	 * COMMENT
	 * 
	 * @param value COMMENT
	 */
	public AtomObjectExpr(Object value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field COMMENT
	 * @param preFields COMMENT
	 */
	public AtomObjectExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		if (this.isFinishedType()) {
			if (this.getValue() != null)
				return this.getValue().getClass();
			else
				return null;
		} else
			return this.getField().getType();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomObjectExpr clone() {
		if (this.isFinishedType())
			return new AtomObjectExpr(this.getValue());
		else {
			AtomObjectExpr expr = new AtomObjectExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
