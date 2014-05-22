package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.Map;

/**
 * 
 * @author Max Nitze
 */
public class AbstractNotConstraint extends AbstractConstraint {
	/**  */
	public AbstractConstraint constraint;

	/**
	 * 
	 * @param constraint
	 */
	public AbstractNotConstraint(AbstractConstraint constraint) {
		this.preFields.addAll(constraint.preFields);

		this.constraint = constraint;
	}

	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraint.replaceAll(regex, replacement);
	}

	@Override
	public void changeStringLiteralType(String regex, Class<?> type) {
		this.constraint.changeStringLiteralType(regex, type);
	}

	@Override
	public AbstractConstraint evaluate() {
		this.constraint = this.constraint.evaluate();

		if (this.constraint instanceof AbstractBooleanConstraint)
			return new AbstractBooleanConstraint(!((AbstractBooleanConstraint) this.constraint).value);
		else
			return this;
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
		this.constraint.substitute(constraintArguments);
	}

	@Override
	public boolean matches(String regex) {
		return this.constraint.matches(regex);
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractNotConstraint))
			return false;

		AbstractNotConstraint abstractNotConstraint = (AbstractNotConstraint) object;

		return this.constraint.equals(abstractNotConstraint.constraint);
	}

	@Override
	public AbstractConstraint clone() {
		return new AbstractNotConstraint(
				this.constraint.clone());
	}

	@Override
	public String toString() {
		return "NOT " + this.constraint.toString();
	}
}
