package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
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

	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraint evaluate() {
		this.value1 = this.value1.evaluate();
		this.value2 = this.value2.evaluate();

		if (!(this.value1 instanceof AbstractConstraintLiteral<?>) || !(this.value2 instanceof AbstractConstraintLiteral<?>))
			return this;

		return ConstraintUtils.evaluate(
				(AbstractConstraintLiteral<?>) this.value1, operator, (AbstractConstraintLiteral<?>) this.value2, this);
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
		this.value1 = this.value1.substitute(constraintArguments);
		this.value2 = this.value2.substitute(constraintArguments);
	}

	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}
	
	@Override
	public AbstractConstraint invert() {
		this.operator = this.operator.getOpposite();
		
		return this;
	}

	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof AbstractSingleConstraint))
			return false;

		AbstractSingleConstraint singleConstraint = (AbstractSingleConstraint) obj;

		return (
				(this.value1.equals(singleConstraint.value1) &&
						this.value2.equals(singleConstraint.value2) &&
						(this.operator == singleConstraint.operator)) ||
				(this.value1.equals(singleConstraint.value2) &&
						this.value2.equals(singleConstraint.value1) &&
						(this.operator == ConstraintOperator.fromSwappedAsciiName(singleConstraint.operator.opcode))));
	}

	@Override
	public AbstractConstraint clone() {
		return new AbstractSingleConstraint(
				this.value1.clone(), this.operator, this.value2.clone(), new ArrayList<PreField>(this.preFields));
	}

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
