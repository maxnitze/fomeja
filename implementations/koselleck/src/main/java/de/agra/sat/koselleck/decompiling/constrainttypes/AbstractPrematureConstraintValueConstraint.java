package de.agra.sat.koselleck.decompiling.constrainttypes;

public class AbstractPrematureConstraintValueConstraint extends AbstractConstraintValue {
	/**  */
	public AbstractConstraint constraint;

	/**
	 * 
	 * @param constraint
	 */
	public AbstractPrematureConstraintValueConstraint(AbstractConstraint constraint) {
		this.constraint = constraint;
	}

	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraint.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraintValue evaluate() {
		this.constraint = this.constraint.evaluate();

		return this;
	}

	@Override
	public boolean matches(String regex) {
		return this.constraint.matches(regex);
	}

	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractPrematureConstraintValueConstraint))
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
