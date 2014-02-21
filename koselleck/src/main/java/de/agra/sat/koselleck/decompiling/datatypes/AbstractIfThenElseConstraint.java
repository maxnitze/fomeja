package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public class AbstractIfThenElseConstraint extends AbstractConstraint {
	/**  */
	public AbstractConstraint ifCondition;
	
	/**  */
	public AbstractConstraint thenCaseConstraint;
	/**  */
	public AbstractConstraint elseCaseConstraint;

	/**
	 * 
	 * @param ifCondition
	 * @param thenCaseConstraint
	 * @param elseCaseConstraint
	 */
	public AbstractIfThenElseConstraint(AbstractConstraint ifCondition, AbstractConstraint thenCaseConstraint, AbstractConstraint elseCaseConstraint) {
		this.ifCondition = ifCondition;
		
		this.thenCaseConstraint = thenCaseConstraint;
		this.elseCaseConstraint = elseCaseConstraint;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.ifCondition.replaceAll(regex, replacement);
		
		this.thenCaseConstraint.replaceAll(regex, replacement);
		this.elseCaseConstraint.replaceAll(regex, replacement);
	}

	/**
	 * 
	 * @param prefixedField
	 * @param replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		this.ifCondition.replaceAll(prefixedField, replacement);
		
		this.thenCaseConstraint.replaceAll(prefixedField, replacement);
		this.elseCaseConstraint.replaceAll(prefixedField, replacement);
	}

	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint evaluate() {
		this.ifCondition = this.ifCondition.evaluate();
		
		if(this.ifCondition instanceof AbstractBooleanConstraint) {
			if(((AbstractBooleanConstraint)this.ifCondition).value)
				return this.thenCaseConstraint.evaluate();
			else
				return this.elseCaseConstraint.evaluate();
		} else {
			this.thenCaseConstraint = this.thenCaseConstraint.evaluate();
			this.elseCaseConstraint = this.elseCaseConstraint.evaluate();
			
//			if(this.thenCaseConstraint instanceof AbstractBooleanConstraint) {
//				if(this.elseCaseConstraint instanceof AbstractBooleanConstraint) {
//					AbstractBooleanConstraint booleanThenCaseConstraint = (AbstractBooleanConstraint)this.thenCaseConstraint;
//					AbstractBooleanConstraint booleanElseCaseConstraint = (AbstractBooleanConstraint)this.elseCaseConstraint;
//					
//					if(booleanThenCaseConstraint.value && booleanElseCaseConstraint.value)
//						return new AbstractBooleanConstraint(true);
//					else if(booleanThenCaseConstraint.value)
//						return this.ifCondition;
//					else if(booleanElseCaseConstraint.value)
//						return this.ifCondition.invert();
//					else
//						return new AbstractBooleanConstraint(false);
//				} else {
//					AbstractBooleanConstraint booleanThenCaseConstraint = (AbstractBooleanConstraint)this.thenCaseConstraint;
//					
//					if(booleanThenCaseConstraint.value)
//						return new AbstractSubConstraint(
//								this.ifCondition,
//								BooleanConnector.OR,
//								new AbstractSubConstraint(
//										this.ifCondition.clone().invert(),
//										BooleanConnector.AND,
//										this.elseCaseConstraint));
//					else
//						return new AbstractSubConstraint(
//								this.ifCondition.clone().invert(),
//								BooleanConnector.AND,
//								this.elseCaseConstraint);
//				}
//			} else if(this.elseCaseConstraint instanceof AbstractBooleanConstraint) {
//				AbstractBooleanConstraint booleanElseCaseConstraint = (AbstractBooleanConstraint)this.elseCaseConstraint;
//				
//				if(booleanElseCaseConstraint.value)
//					return new AbstractSubConstraint(
//							new AbstractSubConstraint(
//									this.ifCondition,
//									BooleanConnector.AND,
//									this.thenCaseConstraint),
//							BooleanConnector.OR,
//							this.ifCondition.clone().invert());
//				else
//					return new AbstractSubConstraint(
//							this.ifCondition,
//							BooleanConnector.AND,
//							this.thenCaseConstraint);
//			} else
				return this;
		}
	}

	/**
	 * 
	 * @param regex
	 * 
	 * @return
	 */
	@Override
	public boolean matches(String regex) {
		return this.ifCondition.matches(regex) ||
				this.thenCaseConstraint.matches(regex) ||
				this.elseCaseConstraint.matches(regex);
	}

	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return this.ifCondition.matches(prefixedField) ||
				this.thenCaseConstraint.matches(prefixedField) ||
				this.elseCaseConstraint.matches(prefixedField);
	}
	
	/**
	 * 
	 */
	@Override
	public AbstractConstraint invert() {
		this.ifCondition = this.ifCondition.invert();
		
		return this;
	}

	/**
	 * 
	 * @param object
	 * 
	 * @return
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractIfThenElseConstraint))
			return false;
		
		AbstractIfThenElseConstraint abstractIfThenElseConstraint = (AbstractIfThenElseConstraint)object;
		
		return this.ifCondition.equals(abstractIfThenElseConstraint.ifCondition) &&
				this.thenCaseConstraint.equals(abstractIfThenElseConstraint.thenCaseConstraint) &&
				this.elseCaseConstraint.equals(abstractIfThenElseConstraint.elseCaseConstraint);
	}

	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint clone() {
		return new AbstractIfThenElseConstraint(
				this.ifCondition.clone(), this.thenCaseConstraint.clone(), this.elseCaseConstraint.clone());
	}

	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("if ");
		stringRepresentation.append(this.ifCondition.toString());
		stringRepresentation.append(" then ");
		stringRepresentation.append(this.thenCaseConstraint.toString());
		stringRepresentation.append(" else ");
		stringRepresentation.append(this.elseCaseConstraint.toString());
		stringRepresentation.append("");
		return stringRepresentation.toString();
	}
}
