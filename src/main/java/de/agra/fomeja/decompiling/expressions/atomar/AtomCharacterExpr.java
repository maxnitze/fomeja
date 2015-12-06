package de.agra.fomeja.decompiling.expressions.atomar;

/* imports */
import java.lang.reflect.Field;

import de.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomCharacterExpr extends AtomExpr<Character> {
	/**
	 * COMMENT
	 * 
	 * @param value
	 */
	public AtomCharacterExpr(Character value) {
		super(value);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param preFields
	 */
	public AtomCharacterExpr(Field field, PreFieldList preFields) {
		super(field, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AtomCharacterExpr(String name) {
		super(name, false);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<Character> getResultType() {
		return Character.class;
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomCharacterExpr clone() {
		if (this.isFinishedType())
			return new AtomCharacterExpr(this.getValue());
		else if (this.getField() != null) {
			AtomCharacterExpr expr =  new AtomCharacterExpr(this.getField(), this.getPreFieldList());
			expr.setName(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		} else {
			AtomCharacterExpr expr =  new AtomCharacterExpr(this.getName());
			expr.setReplacedValue(this.getReplacedValue());
			return expr;
		}
	}
}
