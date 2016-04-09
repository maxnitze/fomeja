package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

import java.lang.reflect.Field;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomFloatExpr extends AtomExpr<Float> {
	/**
	 * COMMENT
	 * 
	 * @param value COMMENT
	 */
	public AtomFloatExpr(Float value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field COMMENT
	 * @param preFields COMMENT
	 */
	public AtomFloatExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 */
	public AtomFloatExpr(String name) {
		super(name, true);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Float.class;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomFloatExpr clone() {
		if (this.isFinishedType())
			return new AtomFloatExpr(this.getValue());
		else if (this.getField() != null) {
			AtomFloatExpr expr = new AtomFloatExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		} else {
			AtomFloatExpr expr = new AtomFloatExpr(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
