package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;

/**
 * AbstractSingleTheorem is a data type that describes a single theorem by its
 *  constraint and the fields of a component.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractSingleTheorem {
	/** the abstract constraint of the theorem */
	public final AbstractConstraint constraint;
	/** array of lists where each list describes the collections to iterate
	 * over the constraint parameters at the index of the list */
	public final List<Field>[] fields;
	
	/**
	 * Constructor for a new abstract single theorem.
	 * 
	 * @param constraint the new constraint
	 * @param fields the new field list array
	 */
	public AbstractSingleTheorem(AbstractConstraint constraint, List<Field>[] fields) {
		this.constraint = constraint;
		this.fields = fields;
	}
}
