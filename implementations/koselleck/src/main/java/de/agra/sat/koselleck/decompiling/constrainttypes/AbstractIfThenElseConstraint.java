package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.Map;


/** imports */
import de.agra.sat.koselleck.types.BooleanConnector;

/**
 * 
 * @author Max Nitze
 */
public class AbstractIfThenElseConstraint extends AbstractConstraint {
	/**  */
	private AbstractConstraint ifCondition;

	/**  */
	private AbstractConstraint thenCaseConstraint;
	/**  */
	private AbstractConstraint elseCaseConstraint;

	/**
	 * 
	 * @param ifCondition
	 * @param thenCaseConstraint
	 * @param elseCaseConstraint
	 */
	public AbstractIfThenElseConstraint(AbstractConstraint ifCondition, AbstractConstraint thenCaseConstraint, AbstractConstraint elseCaseConstraint) {
		this.getPreFields().addAll(ifCondition.getPreFields());
		this.getPreFields().addAll(thenCaseConstraint.getPreFields());
		this.getPreFields().addAll(elseCaseConstraint.getPreFields());

		this.ifCondition = ifCondition;

		this.thenCaseConstraint = thenCaseConstraint;
		this.elseCaseConstraint = elseCaseConstraint;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public AbstractConstraint getIfCondition() {
		return this.ifCondition;
	}

	/**
	 * 
	 * @return
	 */
	public AbstractConstraint getThenCaseConstraint() {
		return this.thenCaseConstraint;
	}

	/**
	 * 
	 * @return
	 */
	public AbstractConstraint getElseCaseConstraint() {
		return this.elseCaseConstraint;
	}

	/** inherited methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.ifCondition.replaceAll(regex, replacement);

		this.thenCaseConstraint.replaceAll(regex, replacement);
		this.elseCaseConstraint.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraint evaluate() {
		this.ifCondition = this.ifCondition.evaluate();

		if (this.ifCondition instanceof AbstractBooleanConstraint) {
			if (((AbstractBooleanConstraint) this.ifCondition).getValue())
				return this.thenCaseConstraint.evaluate();
			else
				return this.elseCaseConstraint.evaluate();
		} else {
			this.thenCaseConstraint = this.thenCaseConstraint.evaluate();
			this.elseCaseConstraint = this.elseCaseConstraint.evaluate();

			if (this.thenCaseConstraint instanceof AbstractBooleanConstraint) {
				if (this.elseCaseConstraint instanceof AbstractBooleanConstraint) {
					AbstractBooleanConstraint booleanThenCaseConstraint = (AbstractBooleanConstraint) this.thenCaseConstraint;
					AbstractBooleanConstraint booleanElseCaseConstraint = (AbstractBooleanConstraint) this.elseCaseConstraint;

					if (booleanThenCaseConstraint.getValue() && booleanElseCaseConstraint.getValue())
						return new AbstractBooleanConstraint(true);
					else if (booleanThenCaseConstraint.getValue())
						return this.ifCondition;
					else if (booleanElseCaseConstraint.getValue())
						return new AbstractNotConstraint(this.ifCondition);
					else
						return new AbstractBooleanConstraint(false);
				} else {
					AbstractBooleanConstraint booleanThenCaseConstraint = (AbstractBooleanConstraint) this.thenCaseConstraint;

					if (booleanThenCaseConstraint.getValue())
						return new AbstractSubConstraint(
								this.ifCondition, BooleanConnector.OR,
								new AbstractSubConstraint(
										new AbstractNotConstraint(
												this.ifCondition), BooleanConnector.AND, this.elseCaseConstraint));
					else
						return new AbstractSubConstraint(
								new AbstractNotConstraint(this.ifCondition), BooleanConnector.AND, this.elseCaseConstraint);
				}
			} else if (this.elseCaseConstraint instanceof AbstractBooleanConstraint) {
				AbstractBooleanConstraint booleanElseCaseConstraint = (AbstractBooleanConstraint) this.elseCaseConstraint;

				if (booleanElseCaseConstraint.getValue())
					return new AbstractSubConstraint(
							new AbstractSubConstraint(
									this.ifCondition, BooleanConnector.AND, this.thenCaseConstraint),
							BooleanConnector.OR,
							new AbstractNotConstraint(this.ifCondition));
				else
					return new AbstractSubConstraint(
							this.ifCondition, BooleanConnector.AND, this.thenCaseConstraint);
			} else
				return this;
		}
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
		this.ifCondition.substitute(constraintArguments);
		this.thenCaseConstraint.substitute(constraintArguments);
		this.elseCaseConstraint.substitute(constraintArguments);
	}

	@Override
	public boolean matches(String regex) {
		return this.ifCondition.matches(regex)
				|| this.thenCaseConstraint.matches(regex)
				|| this.elseCaseConstraint.matches(regex);
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractIfThenElseConstraint))
			return false;

		AbstractIfThenElseConstraint abstractIfThenElseConstraint = (AbstractIfThenElseConstraint)object;

		return this.ifCondition.equals(abstractIfThenElseConstraint.ifCondition) &&
				this.thenCaseConstraint.equals(abstractIfThenElseConstraint.thenCaseConstraint) &&
				this.elseCaseConstraint.equals(abstractIfThenElseConstraint.elseCaseConstraint);
	}

	@Override
	public AbstractConstraint clone() {
		return new AbstractIfThenElseConstraint(
				this.ifCondition.clone(), this.thenCaseConstraint.clone(), this.elseCaseConstraint.clone());
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("if (");
		stringRepresentation.append(this.ifCondition.toString());
		stringRepresentation.append(") then (");
		stringRepresentation.append(this.thenCaseConstraint.toString());
		stringRepresentation.append(") else (");
		stringRepresentation.append(this.elseCaseConstraint.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}
}
