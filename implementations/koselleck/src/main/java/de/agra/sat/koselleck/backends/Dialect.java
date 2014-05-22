package de.agra.sat.koselleck.backends;

/** imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ComplexParameterObject;
import de.agra.sat.koselleck.backends.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.SimpleParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.backends.datatypes.VariableField;
import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractNotConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralString;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintValueException;
import de.agra.sat.koselleck.types.BooleanConnector;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.types.Opcode;
import de.agra.sat.koselleck.utils.CompareUtils;
import de.agra.sat.koselleck.utils.KoselleckUtils;

/**
 * Dialect is an interface for all possible pseudo boolean dialects to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Dialect<T, V> {
	/** dialect types */
	public static enum Type {
		smt,
		smt2,
		dl,
		dimacs
	};

	/** dialect type */
	public final Dialect.Type dialectType;

	/**
	 * Constructor for a new dialect.
	 * 
	 * @param dialectType the type of the dialect
	 */
	public Dialect(Dialect.Type dialectType) {
		this.dialectType = dialectType;
	}

	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * format formats the given list of single theorems to the specific string
	 *  representation of the theorem prover.
	 * 
	 * @param theorem
	 * 
	 * @return the specific string representation of the theorem prover
	 * 
	 * @throws NotSatisfiableException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	public abstract T format(Theorem theorem) throws NotSatisfiableException;

	/**
	 * 
	 * @param resultObject
	 * 
	 * @return
	 */
	public abstract Map<String, Object> parseResult(Object resultObject);

	/** abstract constraints
	 * ----- ----- ----- ----- ----- */

	/**
	 * prepareAbstractBooleanConstraint returns the string representation of a
	 *  given abstract boolean constraint.
	 * 
	 * @param booleanConstraint the abstract boolean constraint to proceed
	 * 
	 * @return the string representation of the abstract boolean constraint
	 */
	public abstract T prepareAbstractBooleanConstraint(AbstractBooleanConstraint booleanConstraint);

	/**
	 * prepareAbstractNotConstraint returns the string representation of a
	 *  given abstract not-constraint.
	 * 
	 * @param booleanConstraint the abstract not-constraint to proceed
	 * 
	 * @return the string representation of the abstract not-constraint
	 */
	public abstract T prepareAbstractNotConstraint(AbstractNotConstraint notConstraint);

	/**
	 * prepareAbstractSingleConstraint returns the string representation of a
	 *  given abstract single constraint.
	 * 
	 * @param singleConstraint the abstract single constraint to proceed
	 * 
	 * @return the string representation of the abstract single constraint
	 */
	public abstract T prepareAbstractSingleConstraint(AbstractSingleConstraint singleConstraint);

	/**
	 * prepareAbstractSubConstraint returns the string representation of a
	 *  given abstract sub constraint.
	 * 
	 * @param subConstraint the abstract sub constraint to proceed
	 * 
	 * @return the string representation of the abstract sub constraint
	 */
	public abstract T prepareAbstractSubConstraint(AbstractSubConstraint subConstraint);

	/**
	 * prepareAbstractIfThenElseConstraint returns the string representation of
	 *  a given abstract if-then-else constraint.
	 * 
	 * @param ifThenElseConstraint the abstract if-then-else constraint to
	 *  proceed
	 * 
	 * @return the string representation of the abstract if-then-else
	 *  constraint
	 */
	public abstract T prepareAbstractIfThenElseConstraint(AbstractIfThenElseConstraint ifThenElseConstraint);

	/** abstract constraint values
	 * ----- ----- ----- ----- ----- */

	/**
	 * prepareAbstractConstraintLiteral returns the string representation of a
	 *  given abstract constraint literal.
	 * 
	 * @param constraintLiteral the abstract constraint literal to proceed
	 * 
	 * @return the string representation of the abstract constraint literal
	 */
	public abstract V prepareAbstractConstraintLiteral(AbstractConstraintLiteral<?> constraintLiteral);

	/**
	 * prepareAbstractConstraintFormula returns the string representation of a
	 *  given abstract constraint formula.
	 * 
	 * @param constraintFormula the abstract constraint formula to proceed
	 * 
	 * @return the string representation of the abstract constraint formula
	 */
	public abstract V prepareAbstractConstraintFormula(AbstractConstraintFormula constraintFormula);

	/** protected methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * getBackendConstraint returns the string representation of a given
	 *  abstract constraint.
	 * 
	 * @param constraint the abstract constraint to proceed
	 * 
	 * @return the string representation of the abstract constraint
	 */
	protected T getBackendConstraint(AbstractConstraint constraint) {
		if (constraint instanceof AbstractBooleanConstraint)
			return prepareAbstractBooleanConstraint((AbstractBooleanConstraint) constraint);
		else if (constraint instanceof AbstractNotConstraint)
			return prepareAbstractNotConstraint((AbstractNotConstraint) constraint);
		else if (constraint instanceof AbstractSingleConstraint)
			return prepareAbstractSingleConstraint((AbstractSingleConstraint) constraint);
		else if (constraint instanceof AbstractSubConstraint)
			return prepareAbstractSubConstraint((AbstractSubConstraint) constraint);
		else if (constraint instanceof AbstractIfThenElseConstraint)
			return prepareAbstractIfThenElseConstraint((AbstractIfThenElseConstraint) constraint);
		else {
			UnsupportedConstraintException exception = new UnsupportedConstraintException(constraint);
			Logger.getLogger(Dialect.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	/**
	 * getBackendConstraint returns the string representation of a given
	 *  abstract constraint value.
	 * 
	 * @param constraintValue the abstract constraint value to proceed
	 * 
	 * @return the string representation of the abstract constraint value
	 */
	protected V getBackendConstraintValue(AbstractConstraintValue constraintValue) {
		if (constraintValue instanceof AbstractConstraintLiteral)
			return prepareAbstractConstraintLiteral((AbstractConstraintLiteral<?>) constraintValue);
		else if (constraintValue instanceof AbstractConstraintFormula)
			return prepareAbstractConstraintFormula((AbstractConstraintFormula) constraintValue);
		else {
			UnsupportedConstraintValueException exception = new UnsupportedConstraintValueException(constraintValue);
			Logger.getLogger(Dialect.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	/**
	 * getConstraintForArguments assigns the given abstract single theorems
	 *  with the non-variable fields of the component.
	 * 
	 * @param component the component to get the arguments from
	 * @param singleTheorems the list of single theorems to assign
	 * 
	 * @return the assigned theorem for the given abstract single theorems and
	 *  the component
	 * 
	 * @throws NotSatisfiableException if there is an assigned constraint that
	 *  is not satisfiable
	 */
	protected Theorem getConstraintForArguments(Object component, List<AbstractSingleTheorem> singleTheorems) throws NotSatisfiableException {
		List<AbstractConstraint> constraints = new ArrayList<AbstractConstraint>();
		List<VariableField> variableFields = new ArrayList<VariableField>();
		Map<String, ParameterObject> variablesMap = new HashMap<String, ParameterObject>();
		Set<AbstractConstraint> objectRangeConstraints = new HashSet<AbstractConstraint>();

		for (AbstractSingleTheorem singleTheorem : singleTheorems) {
			AbstractConstraint constraint = singleTheorem.constraint;

			Set<PreField> preFieldsList = new HashSet<PreField>();
			for (PreField preField : constraint.preFields) {
				if (preField.fieldCode == Opcode.Xload && preField.fieldCodeIndex == 0 && !preField.isVariable && constraint.matches(preField.constantTablePrefixedName))
					constraint.replaceAll(preField.constantTablePrefixedName, this.getAttributeReplacement(component, preField));
				else if (preField.fieldCode == Opcode.Xload && constraint.matches(preField.constantTablePrefixedName))
					if (!preFieldsList.contains(preField))
						preFieldsList.add(preField);
			}

			ConstraintParameter[] constraintParameters = new ConstraintParameter[singleTheorem.fields.length];
			List<Field>[] parameterFields = singleTheorem.fields;
			for (int i = 0; i<singleTheorem.fields.length; i++)
				constraintParameters[i] = new ConstraintParameter(component, i, parameterFields[i]);

			boolean skipTheorem = false;
			for (ConstraintParameter constraintParameter : constraintParameters) {
				if (!constraintParameter.isIncrementable()) {
					skipTheorem = true;
					break;
				}
			}
			if (skipTheorem)
				continue;

			/**  */
			Set<String> complexParameterObjects = new HashSet<String>();

			List<ParameterObject> parameterObjects = new ArrayList<ParameterObject>();
			ParameterObject currentParameterObject = null;

			do {
				AbstractConstraint cConstraint = constraint.clone();

				/** substitute the parameters of the current constraint */
				Map<Integer, Object> constraintParametersMap = new HashMap<Integer, Object>();
				for (int i = 0; i < constraintParameters.length; i++)
					constraintParametersMap.put(i+1, constraintParameters[i].getCurrentCollectionObject());
				cConstraint.substitute(constraintParametersMap);

				/** replace the previous fields in the current constraint */
				for (PreField preField : preFieldsList) {
					ConstraintParameter currentConstraintParameter = constraintParameters[preField.fieldCodeIndex-1];
					if (!preField.isVariable) {
						String replacement = this.getReplacement(preField, currentConstraintParameter.getCurrentCollectionObject());
						cConstraint.replaceAll(preField.constantTablePrefixedName, replacement);
					} else {
						Object parameterObject = this.getParameterObject(preField, currentConstraintParameter.getCurrentCollectionObject());

						int index = -1;
						for (ParameterObject paramObject : parameterObjects) {
							if (paramObject.object.equals(parameterObject) && paramObject.preField.field.equals(preField.field)) {
								currentParameterObject = paramObject;
								index = currentParameterObject.index;
								break;
							}
						}

						/**  */
						if (index == -1) {
							int maxIndex = 0;
							for (ParameterObject paramObject : parameterObjects)
								if (paramObject.preField.field.equals(preField.field))
									maxIndex = (paramObject.index > maxIndex ? paramObject.index : maxIndex);
							index = maxIndex + 1;

							Class<?> variableType = preField.field.getType();
							if (CompareUtils.equalsAny(preField.field.getType(), CompareUtils.booleanClasses)
									|| CompareUtils.equalsAny(preField.field.getType(), CompareUtils.integerClasses)
									|| CompareUtils.equalsAny(preField.field.getType(), CompareUtils.floatClasses)
									|| CompareUtils.equalsAny(preField.field.getType(), CompareUtils.doubleClasses))

								currentParameterObject = new SimpleParameterObject(parameterObject, preField, index);
							else {
								List<Field> collectionFields = KoselleckUtils.getCollectionFields(component.getClass(), preField.field.getGenericType());
								List<Collection<?>> componentCollections = new ArrayList<Collection<?>>();
								int collectionElementsCount = 0;
								for (Field collectionField : collectionFields) {
									try {
										Collection<?> componentCollection = (Collection<?>) collectionField.get(component);
										collectionElementsCount += componentCollection.size();
										componentCollections.add(componentCollection);
									} catch (IllegalArgumentException | IllegalAccessException e) {
										Logger.getLogger(Dialect.class).error("could not get field \"" + collectionField.getName() + "\" for component");
									}
								}

								Set<PreField> currentPreFieldSet = new HashSet<PreField>();
								currentPreFieldSet.add(preField);

								objectRangeConstraints.add(new AbstractSubConstraint(
										new AbstractSingleConstraint(
												new AbstractConstraintLiteralString(preField.preFieldsPrefixedName + "_" + index, Integer.class),
												ConstraintOperator.GREATER_EQUAL,
												new AbstractConstraintLiteralInteger(0), new HashSet<PreField>(currentPreFieldSet)),
										BooleanConnector.AND,
										new AbstractSingleConstraint(
												new AbstractConstraintLiteralString(preField.preFieldsPrefixedName + "_" + index, Integer.class),
												ConstraintOperator.LESS,
												new AbstractConstraintLiteralInteger(collectionElementsCount), new HashSet<PreField>(currentPreFieldSet))));

								variableType = Integer.class;
								complexParameterObjects.add(preField.preFieldsPrefixedName + "_" + index);

								currentParameterObject = new ComplexParameterObject(parameterObject, preField, index, componentCollections);
							}

							parameterObjects.add(currentParameterObject);

							variablesMap.put(preField.preFieldsPrefixedName + "_" + index, currentParameterObject);
							VariableField variableField = new VariableField(preField.preFieldsPrefixedName + "_" + index, variableType);
							if (!variableFields.contains(variableField))
								variableFields.add(variableField);
						}

						cConstraint.replaceAll(preField.constantTablePrefixedName, preField.preFieldsPrefixedName + "_" + index);
					}
				}

				for (String complexParameterObjectName : complexParameterObjects)
					cConstraint.changeStringLiteralType(complexParameterObjectName, Integer.class);

				AbstractConstraint abstractPartialConstraint = cConstraint.evaluate();
				if (abstractPartialConstraint instanceof AbstractBooleanConstraint) {
					AbstractBooleanConstraint abstractBooleanConstraint = (AbstractBooleanConstraint) abstractPartialConstraint;
					if (!abstractBooleanConstraint.value)
						throw new NotSatisfiableException("one or more of the constraints are not satisfiable for the given instance");
				} else
					constraints.add(abstractPartialConstraint);
			} while (KoselleckUtils.incrementIndices(constraintParameters));
		}

		constraints.addAll(objectRangeConstraints);

		return new Theorem(constraints, variableFields, variablesMap);
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * getAttributeReplacement checks if the given prefixed field is an
	 *  attribute type field and returns the replacement for this field.
	 * 
	 * @param component the component to get the replacements from
	 * @param preField the prefixed field to get the replacement for
	 * 
	 * @return the replacement for the attribute field
	 * 
	 * @see Dialect#getReplacement(PrefixedField, Object)
	 * @see Dialect#getParameterObject(PrefixedField, Object)
	 */
	private String getAttributeReplacement(Object component, PreField preField) {
		if (preField.fieldCode != Opcode.Xload || preField.fieldCodeIndex != 0) {
			Logger.getLogger(Dialect.class).fatal("given field \"" + preField.field.getName() + "\" is no attribute field");
			throw new IllegalArgumentException("given field \"" + preField.field.getName() + "\" is no attribute field");
		}

		return this.getReplacement(preField, component);
	}

	/**
	 * getReplacement returns the replacement for the given prefixed field by
	 *  reflectively getting its parameter objects and the value of this for
	 *  the given starting object.
	 * 
	 * @param preField the prefixed field to get the replacement for
	 * @param startingObject the object to start getting its sub-values
	 * 
	 * @return the replacement for the given prefixed field
	 * 
	 * @see Dialect#getParameterObject(PrefixedField, Object)
	 */
	private String getReplacement(PreField preField, Object startingObject) {
		Object replacement = this.getParameterObject(preField, startingObject);

		preField.field.setAccessible(true);
		try{
			replacement = preField.field.get(replacement);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			Logger.getLogger(Dialect.class).fatal("could not access field \"" + preField.field.getName() +"\"");
			throw new IllegalArgumentException("could not access field \"" + preField.field.getName() +"\"");
		}

		return replacement.toString();
	}

	/**
	 * getParameterObject returns the object for the given prefixed field by
	 *  reflectively getting its parameter objects for the given starting
	 *  object.
	 * 
	 * @param preField the prefixed field to get the parameter object for
	 * @param startingObject the object to start getting its sub-values
	 * 
	 * @return the parameter object for the given prefixed field
	 */
	private Object getParameterObject(PreField preField, Object startingObject) {
		Object parameterObject = startingObject;
		for (PreField prePreField : preField.preFields) {
			prePreField.field.setAccessible(true);
			try {
				parameterObject = prePreField.field.get(parameterObject);
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not access field \"" + prePreField.field.getName() +"\" on object \"" + startingObject + "\"";
				Logger.getLogger(Dialect.class).fatal(message);
				throw new IllegalArgumentException(message + "\n" + e.getMessage());
			}
		}

		return parameterObject;
	}
}
