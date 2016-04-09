package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

import java.lang.reflect.Field;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomEnumExpr extends AtomExpr<Enum<?>> {
	/**
	 * COMMENT
	 * 
	 * @param value COMMENT
	 */
	public AtomEnumExpr(Enum<?> value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field COMMENT
	 * @param preFields COMMENT
	 */
	public AtomEnumExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		if (this.isFinishedType())
			return this.getValue().getClass();
		else
			return this.getField().getClass();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomEnumExpr clone() {
		if (this.isFinishedType())
			return new AtomEnumExpr(this.getValue());
		else {
			AtomEnumExpr expr = new AtomEnumExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
