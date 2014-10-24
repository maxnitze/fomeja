package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.util.Map;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;

public class AbstractPrematureConstraintValueConstraint extends AbstractConstraintValue {
	/**  */
	private AbstractConstraint constraint;

	/**
	 * 
	 * @param constraint
	 */
	public AbstractPrematureConstraintValueConstraint(AbstractConstraint constraint) {
		this.constraint = constraint;
	}

	/** inherited methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public AbstractConstraint getConstraint() {
		return this.constraint;
	}

	/** inherited methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraint.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraintValue evaluate() {
		this.constraint = this.constraint.evaluate();

		if (this.constraint instanceof AbstractBooleanConstraint)
			return ((AbstractBooleanConstraint) this.constraint).getReturnValue().evaluate();
		else
			return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		this.constraint.substitute(constraintArguments);

		return this;
	}

	@Override
	public boolean matches(String regex) {
		return this.constraint.matches(regex);
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractPrematureConstraintValueConstraint))
			return false;

		AbstractPrematureConstraintValueConstraint constraintValue = (AbstractPrematureConstraintValueConstraint) object;

		return this.constraint.equals(constraintValue.constraint);
	}

	@Override
	public AbstractConstraintValue clone() {
		return new AbstractPrematureConstraintValueConstraint(this.constraint.clone());
	}

	@Override
	public String toString() {
		return this.constraint.toString();
	}

}
