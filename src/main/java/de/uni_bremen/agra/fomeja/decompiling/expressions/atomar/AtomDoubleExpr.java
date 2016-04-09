package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

/* imports */
import java.lang.reflect.Field;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomDoubleExpr extends AtomExpr<Double> {
	/**
	 * COMMENT
	 * 
	 * @param value COMMENT
	 */
	public AtomDoubleExpr(Double value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field COMMENT
	 * @param preFields COMMENT
	 */
	public AtomDoubleExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 */
	public AtomDoubleExpr(String name) {
		super(name, true);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return Double.class;
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomDoubleExpr clone() {
		if (this.isFinishedType())
			return new AtomDoubleExpr(this.getValue());
		else if (this.getField() != null) {
			AtomDoubleExpr expr = new AtomDoubleExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		} else {
			AtomDoubleExpr expr = new AtomDoubleExpr(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
