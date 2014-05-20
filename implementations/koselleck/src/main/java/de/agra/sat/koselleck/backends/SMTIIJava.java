package de.agra.sat.koselleck.backends;

import java.util.Map;

import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractNotConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractPrematureConstraintValueAccessibleObject;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractPrematureConstraintValueConstraint;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;

public class SMTIIJava extends Dialect {
	/**
	 * 
	 */
	public SMTIIJava() {
		super(Type.smt2);
	}

	@Override
	public String format(Theorem theorem) throws NotSatisfyableException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<String, Object> parseResult(String result) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractBooleanConstraint(
			AbstractBooleanConstraint booleanConstraint) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractNotConstraint(
			AbstractNotConstraint notConstraint) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractSingleConstraint(
			AbstractSingleConstraint singleConstraint) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractSubConstraint(
			AbstractSubConstraint subConstraint) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractIfThenElseConstraint(
			AbstractIfThenElseConstraint ifThenElseConstraint) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractConstraintLiteral(
			AbstractConstraintLiteral<?> constraintLiteral) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractConstraintFormula(
			AbstractConstraintFormula constraintFormula) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractPrematureConstraintValueAccessibleObject(
			AbstractPrematureConstraintValueAccessibleObject prematureConstraintValueAccessibleObject) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String prepareAbstractPrematureConstraintValueConstraint(
			AbstractPrematureConstraintValueConstraint prematureConstraintValueConstraint) {
		// TODO Auto-generated method stub
		return null;
	}
}
