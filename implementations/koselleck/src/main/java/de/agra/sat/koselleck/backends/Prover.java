package de.agra.sat.koselleck.backends;

/** imports */
import java.lang.reflect.Field;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.BasicParameterObject;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.RangedParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.datatypes.PreFieldList;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;

/**
 * Prover is an interface for all possible theorem provers to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Prover<T extends Dialect<?, ?>> {
	/** the dialect of the prover */
	private final T dialect;

	/**
	 * Constructor for a new prover.
	 * 
	 * @param dialect the dialect of the new prover
	 */
	public Prover(T dialect) {
		this.dialect = dialect;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public T getDialect() {
		return this.dialect;
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * solveAndAssign solves the theorem given by the single theorems using the
	 *  prover (needs to be an smt2 prover). Afterwards the solved
	 *  configuration is assigned to the parameter object of the theorem.
	 * 
	 * @param component the objects to get the arguments from
	 * @param singleTheorems the single theorems to solve and assign
	 * 
	 * @throws NotSatisfiableException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	public abstract void solveAndAssign(Object component, List<AbstractSingleTheorem> singleTheorems) throws NotSatisfiableException;

	/**
	 * COMMENT
	 * 
	 * @param theorem
	 * @param proverResults
	 */
	void assign(Theorem theorem, Map<String, Object> proverResults) {
		for (ParameterObject parameterObject : theorem.getVariablesMap().values())
			if (!parameterObject.isAssigned())
				this.assign(proverResults, parameterObject);
	}

	/**
	 * COMMENT
	 * 
	 * @param proverResults
	 * @param parameterObject
	 */
	private void assign(Map<String, Object> proverResults, ParameterObject parameterObject) {
		Object proverResult = proverResults.get(parameterObject.getName());
		if (proverResult != null) {
			if (parameterObject.isDependend() && !parameterObject.getDependentParameterObject().isAssigned())
				this.assign(proverResults, parameterObject.getDependentParameterObject());

			this.assignVariable(parameterObject,
					this.getFieldValue(parameterObject.getPreFieldList().head(-1), parameterObject.getObject()), proverResult);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param parameterObject
	 * @param fieldObject
	 * @param proverResult
	 */
	private void assignVariable(ParameterObject parameterObject, Object fieldObject, Object proverResult) {
		Field field = parameterObject.getPreFieldList().last().getField();
		boolean accessibility = field.isAccessible(); 
		field.setAccessible(true);
		try {
			if (parameterObject instanceof BasicParameterObject)
				field.set(fieldObject, proverResult);
			else if (parameterObject instanceof RangedParameterObject) {
				field.set(fieldObject,
						((RangedParameterObject) parameterObject).getObjectRangeElement((Integer) proverResult));
			}

			parameterObject.setAssigned();
		} catch (IllegalArgumentException | IllegalAccessException e) {
			String message = "could not access field \"" + field.getName() +"\"";
			Logger.getLogger(Prover.class).fatal(message);
			throw new IllegalArgumentException(message);
		} finally {
			field.setAccessible(accessibility);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 * @param startingObject
	 * 
	 * @return
	 */
	private Object getFieldValue(PreFieldList preFieldList, Object startingObject) {
		Object object = startingObject;
		for (PreField preField : preFieldList)
			object = this.getFieldValue(preField.getField(), object);

		return object;
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param object
	 * 
	 * @return
	 */
	private Object getFieldValue(Field field, Object object) {
		boolean accessibility = field.isAccessible();
		field.setAccessible(true);
		try {
			return field.get(object);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			String message = "could not access field \"" + field.getName() + "\" on object \"" + object + "\"";
			Logger.getLogger(Dialect.class).fatal(message);
			throw new IllegalArgumentException(message + "\n" + e.getMessage());
		} finally {
			field.setAccessible(accessibility);
		}
	}
}