package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public class AbstractIfThenElseConstraint extends AbstractConstraint {
	/**  */
	public AbstractConstraint ifConstraint;
	
	/**  */
	public AbstractConstraint thenCaseConstraint;
	/**  */
	public AbstractConstraint elseCaseConstraint;

	/**
	 * 
	 * @param ifConstraint
	 * @param thenCaseConstraint
	 * @param elseCaseConstraint
	 */
	public AbstractIfThenElseConstraint(AbstractConstraint ifConstraint, AbstractConstraint thenCaseConstraint, AbstractConstraint elseCaseConstraint) {
		this.ifConstraint = ifConstraint;
		
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
		this.ifConstraint.replaceAll(regex, replacement);
		
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
		this.ifConstraint.replaceAll(prefixedField, replacement);
		
		this.thenCaseConstraint.replaceAll(prefixedField, replacement);
		this.elseCaseConstraint.replaceAll(prefixedField, replacement);
	}

	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint evaluate() {
		this.ifConstraint = this.ifConstraint.evaluate();
		
		if(this.ifConstraint instanceof AbstractBooleanConstraint) {
			if(((AbstractBooleanConstraint)this.ifConstraint).value)
				return this.thenCaseConstraint.evaluate();
			else
				return this.elseCaseConstraint.evaluate();
		} else {
			this.thenCaseConstraint = this.thenCaseConstraint.evaluate();
			this.elseCaseConstraint = this.elseCaseConstraint.evaluate();
			
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
		return this.ifConstraint.matches(regex) ||
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
		return this.ifConstraint.matches(prefixedField) ||
				this.thenCaseConstraint.matches(prefixedField) ||
				this.elseCaseConstraint.matches(prefixedField);
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
		
		return this.ifConstraint.equals(abstractIfThenElseConstraint.ifConstraint) &&
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
				this.ifConstraint.clone(), this.thenCaseConstraint.clone(), this.elseCaseConstraint.clone());
	}

	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("if ");
		stringRepresentation.append(this.ifConstraint.toString());
		stringRepresentation.append(" then ");
		stringRepresentation.append(this.thenCaseConstraint.toString());
		stringRepresentation.append(" else ");
		stringRepresentation.append(this.elseCaseConstraint.toString());
		stringRepresentation.append("");
		return stringRepresentation.toString();
	}
}
