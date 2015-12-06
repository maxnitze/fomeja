package de.agra.fomeja.decompiling.expressions.atomar;

/* imports */
import java.lang.reflect.Field;

import de.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomFloatExpr extends AtomExpr<Float> {
	/**
	 * COMMENT
	 * 
	 * @param value
	 */
	public AtomFloatExpr(Float value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param preFields
	 */
	public AtomFloatExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AtomFloatExpr(String name) {
		super(name, true);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Float.class;
	}

	/** overridden object methods
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