package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

/* imports */
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
	 * @param value
	 */
	public AtomEnumExpr(Enum<?> value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param preFields
	 */
	public AtomEnumExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		if (this.isFinishedType())
			return this.getValue().getClass();
		else
			return this.getField().getClass();
	}

	/** overridden object methods
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
