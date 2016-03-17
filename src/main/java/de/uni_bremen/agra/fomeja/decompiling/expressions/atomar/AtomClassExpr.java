package de.uni_bremen.agra.fomeja.decompiling.expressions.atomar;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AtomClassExpr extends AtomExpr<Class<?>> {

	/**
	 * COMMENT
	 * 
	 * @param value COMMENT
	 */
	public AtomClassExpr(Class<?> value) {
		super(value);
		this.setUnfinished();
	}

	/** inherited methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.getValue();
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AtomClassExpr clone() {
		return new AtomClassExpr(this.getValue());
	}

	@Override
	public String toString() {
		return "CLASS_" + this.getValue().getSimpleName();
	}
}
