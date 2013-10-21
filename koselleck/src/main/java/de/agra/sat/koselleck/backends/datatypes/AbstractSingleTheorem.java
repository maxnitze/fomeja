package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;

/**
 * 
 * @author Max Nitze
 */
public class AbstractSingleTheorem {
	/**  */
	public final AbstractConstraint constraint;
	/**  */
	public final List<Field>[] fields;
	
	/**
	 * 
	 * @param constraint
	 * @param fields
	 */
	public AbstractSingleTheorem(AbstractConstraint constraint, List<Field>[] fields) {
		this.constraint = constraint;
		this.fields = fields;
	}
}
