package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.ArrayList;
import java.util.List;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.utils.ConstraintUtils;

/**
 * AbstractSingleConstraint represents a single constraint in a constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractSingleConstraint extends AbstractConstraint {
	/** the first value */
	public AbstractConstraintValue value1;
	/** the constraint operator of the values */
	public ConstraintOperator operator;
	/** the second value */
	public AbstractConstraintValue value2;
	
	/**
	 * Constructor for a new abstract single constraint.
	 * 
	 * @param value1 the new first value
	 * @param operator the new constraint operator of the values
	 * @param value2 the new second value
	 */
	public AbstractSingleConstraint(AbstractConstraintValue value1, ConstraintOperator operator, AbstractConstraintValue value2, List<PreField> preFields) {
		this.preFields.addAll(preFields);
		
		this.value1 = value1;
		this.operator = operator;
		this.value2 = value2;
	}

	/**
	 * replaceAll replaces all occurrences of the given regular expression
	 *  {@code regex} with the given replacement {@code replacement} by calling
	 *  the replaceAll(String, String) method of the two values.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the replacement
	 * 
	 * @see AbstractConstraintValue#replaceAll(String, String)
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}

	/**
	 * evaluate evaluates this abstract single constraint. At first both values
	 *  are evaluated. If these new values are of type integer afterwards the
	 *  boolean value of this single constraint is calculated. If the values
	 *  are both strings/variables and they are equal the boolean value of
	 *  this single constraint is calculated. Otherwise this abstract single
	 *  constraint is returned.
	 * 
	 * @return the boolean value of this single constraint if possible to
	 *  calculate, this abstract single constraint otherwise
	 */
	@Override
	public AbstractConstraint evaluate() {
		this.value1 = this.value1.evaluate();
		this.value2 = this.value2.evaluate();

		if (!(this.value1 instanceof AbstractConstraintLiteral<?>) || !(this.value2 instanceof AbstractConstraintLiteral<?>))
			return this;

		return ConstraintUtils.evaluate(
				(AbstractConstraintLiteral<?>) this.value1, operator, (AbstractConstraintLiteral<?>) this.value2, this);
	}
	
	/**
	 * matches checks if one or both of the values match the given regular
	 *  expression {@code regex}.
	 * 
	 * @param regex the regular expression to look for
	 * 
	 * @return {@code true} if one or both of the values match the given
	 *  regular expression {@code regex}, {@code false} otherwise
	 */
	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}
	
	@Override
	public AbstractConstraint invert() {
		this.operator = this.operator.getOpposite();
		
		return this;
	}
	
	/**
	 * equals checks if this abstract single constraint and the given object
	 *  are equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object matches this abstract
	 *  single constraint, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof AbstractSingleConstraint))
			return false;
		
		AbstractSingleConstraint singleConstraint = (AbstractSingleConstraint) obj;
		
		System.out.println("TEST123");
		
		return (
				(this.value1.equals(singleConstraint.value1) &&
						this.value2.equals(singleConstraint.value2) &&
						(this.operator == singleConstraint.operator)) ||
				(this.value1.equals(singleConstraint.value2) &&
						this.value2.equals(singleConstraint.value1) &&
						(this.operator == ConstraintOperator.fromSwappedAsciiName(singleConstraint.operator.opcode))));
	}
	
	/**
	 * clone returns a copy of this abstract single constraint.
	 * 
	 * @return a copy of this abstract single constraint
	 */
	@Override
	public AbstractConstraint clone() {
		return new AbstractSingleConstraint(
				this.value1.clone(), this.operator, this.value2.clone(), new ArrayList<PreField>(this.preFields));
	}
	
	/**
	 * toString returns the string representation of this abstract single
	 *  constraint.
	 * 
	 * @return the string representation of this abstract single constraint
	 */
	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append(this.value1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.operator.asciiName);
		stringRepresentation.append(" ");
		stringRepresentation.append(this.value2.toString());
		return stringRepresentation.toString();
	}
}
