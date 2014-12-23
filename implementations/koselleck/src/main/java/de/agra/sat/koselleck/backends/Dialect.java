package de.agra.sat.koselleck.backends;

/** imports */
import java.lang.reflect.Field;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractConstraintSet;
import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.BasicParameterObject;
import de.agra.sat.koselleck.backends.datatypes.ComponentCollectionList;
import de.agra.sat.koselleck.backends.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.ParameterObjectList;
import de.agra.sat.koselleck.backends.datatypes.RangedParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.datatypes.PreFieldList;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractNotConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraintSet;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralDouble;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralFloat;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;
import de.agra.sat.koselleck.exceptions.ParameterObjectException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintValueException;
import de.agra.sat.koselleck.types.BooleanConnector;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.types.Opcode;
import de.agra.sat.koselleck.utils.ClassUtils;
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
	private final Dialect.Type dialectType;

	/**
	 * Constructor for a new dialect.
	 * 
	 * @param dialectType the type of the dialect
	 */
	public Dialect(Dialect.Type dialectType) {
		this.dialectType = dialectType;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public Dialect.Type getDialectType() {
		return this.dialectType;
	}

	/* abstract methods
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

	/* abstract constraints
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
	 * COMMENT
	 * 
	 * @param subConstraintSet
	 * 
	 * @return
	 */
	public abstract T prepareAbstractSubConstraintSet(AbstractSubConstraintSet subConstraintSet);

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

	/* abstract constraint values
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

	/* protected methods
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
		else if (constraint instanceof AbstractSubConstraintSet)
			return prepareAbstractSubConstraintSet((AbstractSubConstraintSet) constraint);
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
		AbstractConstraintSet constraintSet = new AbstractConstraintSet();

		Map<String, ParameterObject> variablesMap = new HashMap<String, ParameterObject>();

		for (AbstractSingleTheorem singleTheorem : singleTheorems) {
			AbstractConstraint constraint = singleTheorem.getConstraint();

			Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiteralSet = new HashSet<AbstractConstraintLiteral<?>>();
			for (AbstractConstraintLiteral<?> unfinishedConstraintLiteral : constraint.getUnfinishedConstraintLiterals()) {
				if (!unfinishedConstraintLiteral.isVariable() && unfinishedConstraintLiteral.getOpcode() == Opcode.Xload && unfinishedConstraintLiteral.getFieldCodeIndex() == 0)
					constraint.replaceAll(unfinishedConstraintLiteral.getName(), this.getReplacement(unfinishedConstraintLiteral, component, true));
				else if (unfinishedConstraintLiteral.getOpcode() == Opcode.Xload)
					unfinishedConstraintLiteralSet.add(unfinishedConstraintLiteral);
			}

			ConstraintParameter[] constraintParameters = new ConstraintParameter[singleTheorem.getFields().length];
			List<Field>[] parameterFields = singleTheorem.getFields();
			for (int i = 0; i<singleTheorem.getFields().length; i++)
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

			do {
				AbstractConstraint clonedConstraint = constraint.clone();

				/* substitute the parameters of the current constraint */
				Map<Integer, Object> constraintParametersMap = new HashMap<Integer, Object>();
				for (int i = 0; i < constraintParameters.length; i++)
					constraintParametersMap.put(i+1, constraintParameters[i].getCurrentCollectionObject());
				clonedConstraint.substitute(constraintParametersMap);

				/* replace the previous fields in the current constraint */
				for (AbstractConstraintLiteral<?> unfinishedConstraintLiteral : unfinishedConstraintLiteralSet) {
					ConstraintParameter currentConstraintParameter = constraintParameters[unfinishedConstraintLiteral.getFieldCodeIndex()-1];

					/* neither literal nor its prefields variable */
					if (!unfinishedConstraintLiteral.isVariable() && !unfinishedConstraintLiteral.getPreFieldList().isVariable()) {
						String replacement = this.getReplacement(unfinishedConstraintLiteral, currentConstraintParameter.getCurrentCollectionObject(), false);
						clonedConstraint.replaceAll(unfinishedConstraintLiteral.getName(), replacement);
					}
					/** COMMENT */
					else {
						PreFieldList preFieldList = unfinishedConstraintLiteral.getPreFieldList();
						ParameterObjectList parameterObjectList = new ParameterObjectList();

						int index = 0;
						boolean isFirstVariable = true;
						Object object = currentConstraintParameter.getCurrentCollectionObject();
						int offsetIndex = preFieldList.size();
						RangedParameterObject prevParameterObject = null;
						for (PreField preField : preFieldList) {
							if (!preField.isVariable() && isFirstVariable)
								object = this.getFieldValue(preField.getField(), object);

							if (preField.isVariable()) {
								if (isFirstVariable) {
									offsetIndex = index;
									isFirstVariable = false;
								}

								PreFieldList headPreFieldList = preFieldList.head(index+1);
								ParameterObject parameterObject = parameterObjectList.get(object, headPreFieldList);
								if (parameterObject == null) {
									parameterObject = this.getNewParameterObject(object, headPreFieldList, prevParameterObject, component);
									parameterObjectList.add(parameterObject);
									if (parameterObject instanceof RangedParameterObject)
										constraintSet.addRangeConstraint(
												this.getRangeConstraint(parameterObject.getName(),
														((RangedParameterObject) parameterObject).getRangeSize()));
									else {
										RuntimeException exception = new ParameterObjectException(parameterObject, "expected ranged parameter object");
										Logger.getLogger(Dialect.class).fatal(exception.getMessage());
										throw exception;
									}
								}

								if (!(parameterObject instanceof RangedParameterObject)) {
									RuntimeException exception = new ParameterObjectException(parameterObject, "expected ranged parameter object");
									Logger.getLogger(Dialect.class).fatal(exception.getMessage());
									throw exception;
								}

								prevParameterObject = (RangedParameterObject) parameterObject;
							}

							++index;
						}

						PreFieldList offsetPreFieldList = preFieldList.tail(offsetIndex);
						offsetPreFieldList.add(unfinishedConstraintLiteral.toPreField());

						ParameterObject parameterObject = parameterObjectList.get(object, offsetPreFieldList);
						if (parameterObject == null) {
							parameterObject = this.getNewParameterObject(object, offsetPreFieldList, prevParameterObject, component);
							parameterObjectList.add(parameterObject);
							if (unfinishedConstraintLiteral.isVariable() && parameterObject instanceof RangedParameterObject)
								constraintSet.addRangeConstraint(
										this.getRangeConstraint(parameterObject.getName(),
												((RangedParameterObject) parameterObject).getRangeSize()));
						}

						for (ParameterObject paramObject : parameterObjectList)
							if (paramObject != null && !variablesMap.containsKey(paramObject.getName()))
								variablesMap.put(paramObject.getName(), paramObject);

						if (!unfinishedConstraintLiteral.isVariable())
							constraintSet.addConnectionConstraint(this.getConnectionConstraint(parameterObject));

						clonedConstraint.replaceAll(unfinishedConstraintLiteral.getName(), parameterObject.getName());
					}
				}

				constraintSet.addBasicConstraint(clonedConstraint.evaluate());
			} while (KoselleckUtils.incrementIndices(constraintParameters));
		}

		return new Theorem(constraintSet.toConstraintList(), variablesMap);
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param dependentParameterObject
	 * @param component
	 * 
	 * @return
	 */
	private ParameterObject getNewParameterObject(Object object, PreFieldList preFields, RangedParameterObject dependentParameterObject, Object component) {
		Field field = preFields.last().getField();
		if (ClassUtils.isBasicClass(field.getType()))
			return new BasicParameterObject(object, preFields, dependentParameterObject);
		else
			return new RangedParameterObject(object, preFields, this.getComponentCollection(component, field), dependentParameterObject);
	}

	/**
	 * COMMENT
	 * 
	 * @param component
	 * @param literalPreField
	 * 
	 * @return
	 */
	private ComponentCollectionList getComponentCollection(Object component, Field field) {
		ComponentCollectionList componentCollections = new ComponentCollectionList();

		/* get list of component-collections for type of field */
		List<Field> collectionFields = KoselleckUtils.getCollectionFields(component.getClass(), field.getGenericType());
		for (Field collectionField : collectionFields) {
			try {
				componentCollections.add((Collection<?>) collectionField.get(component));
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not get field \"" + collectionField.getName() + "\" for component";
				Logger.getLogger(Dialect.class).error(message);
				throw new IllegalArgumentException(message);
			}
		}

		return componentCollections;
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param upperBound
	 * 
	 * @return
	 */
	private AbstractConstraint getRangeConstraint(String name, int upperBound) {
		AbstractConstraintLiteralInteger rangeLiteralInteger = new AbstractConstraintLiteralInteger(name);
		return new AbstractSubConstraint(
				new AbstractSingleConstraint(
						rangeLiteralInteger,
						ConstraintOperator.GREATER_EQUAL,
						new AbstractConstraintLiteralInteger(0)),
				BooleanConnector.AND,
				new AbstractSingleConstraint(
						rangeLiteralInteger,
						ConstraintOperator.LESS,
						new AbstractConstraintLiteralInteger(upperBound)));
	}

	/**
	 * COMMENT
	 * 
	 * @param parameterObject
	 * 
	 * @return
	 */
	private AbstractConstraint getConnectionConstraint(ParameterObject parameterObject) {
		if (parameterObject.getObject() != parameterObject.getDependentParameterObject().getObject()) {
			RuntimeException exception = new ParameterObjectException(parameterObject, "connection constraints need to made on matching objects");
			Logger.getLogger(Dialect.class).fatal(exception.getMessage());
			throw exception;
		} else if (!parameterObject.getPreFieldList().isListPrefix(parameterObject.getDependentParameterObject().getPreFieldList())) {
			RuntimeException exception = new ParameterObjectException(parameterObject, "field list of dependent object needs to be prefix of field list of current object");
			Logger.getLogger(Dialect.class).fatal(exception.getMessage());
			throw exception;
		}

		RangedParameterObject prevParameterObject = parameterObject.getDependentParameterObject();

		PreFieldList preFieldListSuffix = parameterObject.getPreFieldList().tail(prevParameterObject.getPreFieldList().size()+1);
		List<AbstractConstraint> connections = new LinkedList<AbstractConstraint>();

		AbstractConstraintLiteralInteger prevParameterObjectLiteralInteger = new AbstractConstraintLiteralInteger(prevParameterObject.getName());
		Class<?> parameterObjectType = parameterObject.getPreFieldList().last().getField().getType();
		AbstractConstraintLiteral<?> parameterObjectLiteral;
		if (parameterObjectType.equals(Double.class))
			parameterObjectLiteral = new AbstractConstraintLiteralDouble(parameterObject.getName());
		else if (parameterObjectType.equals(Float.class))
			parameterObjectLiteral = new AbstractConstraintLiteralFloat(parameterObject.getName());
		else
			parameterObjectLiteral = new AbstractConstraintLiteralInteger(parameterObject.getName());

		for (int i=0; i<prevParameterObject.getRangeSize(); i++) {
			Object connectionObject = this.getFieldValue(preFieldListSuffix, prevParameterObject.getObjectRangeElement(i));
			AbstractConstraintLiteral<?> connectionLiteral;
			if (parameterObjectType.equals(Double.class))
				connectionLiteral = new AbstractConstraintLiteralDouble((Double) connectionObject);
			else if (parameterObjectType.equals(Float.class))
				connectionLiteral = new AbstractConstraintLiteralFloat((Float) connectionObject);
			else if (parameterObjectType.equals(Integer.class))
				connectionLiteral = new AbstractConstraintLiteralInteger((Integer) connectionObject);
			else
				connectionLiteral = new AbstractConstraintLiteralInteger(parameterObject.getMapping(connectionObject));
			

			connections.add(new AbstractSubConstraint(
					new AbstractSingleConstraint(
							prevParameterObjectLiteralInteger, ConstraintOperator.EQUAL, new AbstractConstraintLiteralInteger(i)),
					BooleanConnector.AND,
					new AbstractSingleConstraint(
							parameterObjectLiteral, ConstraintOperator.EQUAL, connectionLiteral)));
		}

		return new AbstractSubConstraintSet(connections, BooleanConnector.OR);
	}

	/**
	 * COMMENT
	 * 
	 * @param abstractConstraintLiteral
	 * @param startingObject
	 * @param isAttribute
	 * 
	 * @return the replacement for the given abstract constraint literal
	 */
	private String getReplacement(AbstractConstraintLiteral<?> abstractConstraintLiteral, Object startingObject, boolean isAttribute) {
		if (isAttribute &&
				(abstractConstraintLiteral.getOpcode() != Opcode.Xload || abstractConstraintLiteral.getFieldCodeIndex() != 0)) {
			String message = "given field \"" + abstractConstraintLiteral.getField().getName() + "\" is no attribute field";
			Logger.getLogger(Dialect.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		return this.getFieldValue(abstractConstraintLiteral.getField(),
				this.getFieldValue(abstractConstraintLiteral.getPreFieldList(), startingObject)).toString();
	}

	/**
	 * COMMENT
	 * 
	 * @param preFields
	 * @param startingObject
	 * 
	 * @return
	 */
	private Object getFieldValue(List<PreField> preFields, Object startingObject) {
		Object object = startingObject;

		for (PreField preField : preFields)
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
