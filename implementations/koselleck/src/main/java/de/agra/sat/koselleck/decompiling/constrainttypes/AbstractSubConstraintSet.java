package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.types.BooleanConnector;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractSubConstraintSet extends AbstractConstraint {
	/** COMMENT */
	private List<AbstractConstraint> constraints;
	/** the boolean connector of both constraints */
	private final BooleanConnector connector;

	/**
	 * COMMENT
	 * 
	 * @param constraints
	 * @param connector
	 */
	public AbstractSubConstraintSet(List<AbstractConstraint> constraints, BooleanConnector connector) {
		this.constraints = constraints;
		this.connector = connector;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public List<AbstractConstraint> getConstraints() {
		return this.constraints;
	}

	/**
	 * 
	 * @return
	 */
	public BooleanConnector getConnector() {
		return this.connector;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		for (AbstractConstraint constraint : this.constraints)
			constraint.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraint evaluate() {
		for (int i=0; i<this.constraints.size(); i++)
			this.constraints.set(i, this.constraints.get(i).evaluate());

		if (this.constraints.isEmpty())
			return new AbstractBooleanConstraint(true);
		else if (this.constraints.size() == 1)
			return this.constraints.get(0);
		else if (this.constraints.size() == 2)
			return new AbstractSubConstraint(this.constraints.get(0), this.connector, this.constraints.get(1));

		List<AbstractConstraint> newConstraints = new LinkedList<AbstractConstraint>();
		for (AbstractConstraint constraint : this.constraints) {
			if (this.connector == BooleanConnector.AND) {
				if (constraint instanceof AbstractBooleanConstraint)
					if (!((AbstractBooleanConstraint) constraint).getValue())
						return new AbstractBooleanConstraint(false);
				else
					newConstraints.add(constraint);
			} else if (this.connector == BooleanConnector.OR) {
				if (constraint instanceof AbstractBooleanConstraint)
					if (((AbstractBooleanConstraint) constraint).getValue())
						return new AbstractBooleanConstraint(true);
				else
					newConstraints.add(constraint);
			} else {
				RuntimeException exception = new UnknownBooleanConnectorException(this.connector);
				Logger.getLogger(AbstractSubConstraintSet.class).fatal(exception.getMessage());
				throw exception;
			}
		}

		if (newConstraints.isEmpty())
			return new AbstractBooleanConstraint(true);
		else if (newConstraints.size() == 1)
			return newConstraints.get(0);
		else if (newConstraints.size() == 2)
			return new AbstractSubConstraint(newConstraints.get(0), this.connector, newConstraints.get(1));
		else
			return new AbstractSubConstraintSet(newConstraints, this.connector);
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
		for (AbstractConstraint constraint : this.constraints)
			constraint.substitute(constraintArguments);
	}

	@Override
	public boolean matches(String regex) {
		boolean match = false;
		for (AbstractConstraint constraint : this.constraints)
			match |= constraint.matches(regex);
		return match;
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiterals = new HashSet<AbstractConstraintLiteral<?>>();
		for (AbstractConstraint constraint : this.constraints)
			unfinishedConstraintLiterals.addAll(constraint.getUnfinishedConstraintLiterals());

		return unfinishedConstraintLiterals;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractSubConstraintSet))
			return false;

		AbstractSubConstraintSet subConstraintSet = (AbstractSubConstraintSet) object;

		boolean constraintListsAreEqual = this.constraints.size() == subConstraintSet.constraints.size();
		for (AbstractConstraint constraint : this.constraints)
			constraintListsAreEqual &= subConstraintSet.constraints.contains(constraint);

		return constraintListsAreEqual && this.connector == subConstraintSet.connector;
	}

	@Override
	public AbstractConstraint clone() {
		List<AbstractConstraint> clonedConstraints = new LinkedList<AbstractConstraint>();
		for (AbstractConstraint constraint : this.constraints)
			clonedConstraints.add(constraint.clone());

		return new AbstractSubConstraintSet(
				clonedConstraints, this.connector);
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		for (AbstractConstraint constraint : this.constraints) {
			if (stringRepresentation.length() > 0) {
				stringRepresentation.append(" ");
				stringRepresentation.append(this.connector.getCode());
				stringRepresentation.append(" ");
			}
			stringRepresentation.append(constraint.toString());
		}

		return stringRepresentation.toString();
	}
}
