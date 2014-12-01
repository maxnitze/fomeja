package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

import java.util.HashSet;
import java.util.Map;


import java.util.Set;

/** imports */
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * AbstractConstraintFormula represents a formula in a constraint value.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractConstraintFormula extends AbstractConstraintValue {
	/** the first value */
	private AbstractConstraintValue value1;
	/** the second value */
	private AbstractConstraintValue value2;
	/** the arithmetic operator */
	private final ArithmeticOperator operator;

	/**
	 * Constructor for a new AbstractConstraintFormula.
	 * 
	 * @param value1 the new first value
	 * @param operator the new arithmetic operator
	 * @param value2 the new second value
	 */
	public AbstractConstraintFormula(AbstractConstraintValue value1, ArithmeticOperator operator, AbstractConstraintValue value2) {
		this.value1 = value1;
		this.operator = operator;
		this.value2 = value2;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public AbstractConstraintValue getValue1() {
		return this.value1;
	}

	/**
	 * 
	 * @return
	 */
	public AbstractConstraintValue getValue2() {
		return this.value2;
	}

	/**
	 * 
	 * @return
	 */
	public ArithmeticOperator getOperator() {
		return this.operator;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraintValue evaluate() {
		this.value1 = this.value1.evaluate();
		this.value2 = this.value2.evaluate();

		if (this.value1 instanceof AbstractConstraintLiteral<?> && this.value2 instanceof AbstractConstraintLiteral<?>) {
			AbstractConstraintLiteral<?> constraintLiteral1 = (AbstractConstraintLiteral<?>) this.value1;
			AbstractConstraintLiteral<?> constraintLiteral2 = (AbstractConstraintLiteral<?>) this.value2;

			if (constraintLiteral1.isNumberType() && constraintLiteral2.isNumberType())
				return constraintLiteral1.calc(constraintLiteral2, this.operator);
			else
				return this;
		} else
			return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		this.value1 = this.value1.substitute(constraintArguments);
		this.value2 = this.value2.substitute(constraintArguments);

		return this;
	}

	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiterals = new HashSet<AbstractConstraintLiteral<?>>();
		unfinishedConstraintLiterals.addAll(this.value1.getUnfinishedConstraintLiterals());
		unfinishedConstraintLiterals.addAll(this.value2.getUnfinishedConstraintLiterals());

		return unfinishedConstraintLiterals;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintFormula))
			return false;

		AbstractConstraintFormula constraintFormula = (AbstractConstraintFormula)object;

		return this.value1.equals(constraintFormula.value1) 
				&& this.operator == constraintFormula.operator
				&& this.value2.equals(constraintFormula.value2);
	}

	@Override
	public AbstractConstraintValue clone() {
		return new AbstractConstraintFormula(
				this.value1.clone(), this.operator, this.value2.clone());
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("(");
		stringRepresentation.append(this.value1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.operator.getAsciiName());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.value2.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}
}
