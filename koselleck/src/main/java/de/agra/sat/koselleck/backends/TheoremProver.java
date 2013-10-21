package de.agra.sat.koselleck.backends;

/** imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.backends.datatypes.VariableField;
import de.agra.sat.koselleck.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintValue;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.PrefixedField;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintValueException;
import de.agra.sat.koselleck.utils.KoselleckUtils;

/**
 * 
 * @author Max Nitze
 */
public abstract class TheoremProver {
	/** the component to process */
	private Object component;
	
	/** abstract methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param singleTheorems
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException
	 */
	public abstract String format(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException;
	
	/**
	 * 
	 * @param singleTheorems
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException
	 */
	public abstract void solveAndAssign(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException;
	
	/**
	 * 
	 * @param booleanConstraint
	 * 
	 * @return
	 */
	public abstract String prepareAbstractBooleanConstraint(AbstractBooleanConstraint booleanConstraint);
	
	/**
	 * 
	 * @param singleConstraint
	 * 
	 * @return
	 */
	public abstract String prepareAbstractSingleConstraint(AbstractSingleConstraint singleConstraint);
	
	/**
	 * 
	 * @param subConstraint
	 * 
	 * @return
	 */
	public abstract String prepareAbstractSubConstraint(AbstractSubConstraint subConstraint);
	
	/**
	 * 
	 * @param constraintLiteral
	 * 
	 * @return
	 */
	public abstract String prepareAbstractConstraintLiteral(AbstractConstraintLiteral constraintLiteral);
	
	/**
	 * 
	 * @param constraintFormula
	 * 
	 * @return
	 */
	public abstract String prepareAbstractConstraintFormula(AbstractConstraintFormula constraintFormula);
	
	/** protected methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param constraint
	 * 
	 * @return
	 */
	protected String getBackendConstraint(AbstractConstraint constraint) {
		if(constraint instanceof AbstractBooleanConstraint)
			return prepareAbstractBooleanConstraint((AbstractBooleanConstraint)constraint);
		else if(constraint instanceof AbstractSingleConstraint)
			return prepareAbstractSingleConstraint((AbstractSingleConstraint)constraint);
		else if(constraint instanceof AbstractSubConstraint)
			return prepareAbstractSubConstraint((AbstractSubConstraint)constraint);
		else {
			Logger.getLogger(TheoremProver.class).fatal("partial constraint type \"" + (constraint == null ? "null" : constraint.getClass().getSimpleName()) + "\" is not supported");
			throw new UnsupportedConstraintException(constraint);
		}
	}
	
	/**
	 * 
	 * @param constraintValue
	 * 
	 * @return
	 */
	protected String getBackendConstraintValue(AbstractConstraintValue constraintValue) {
		if(constraintValue instanceof AbstractConstraintLiteral)
			return prepareAbstractConstraintLiteral((AbstractConstraintLiteral)constraintValue);
		else if(constraintValue instanceof AbstractConstraintFormula)
			return prepareAbstractConstraintFormula((AbstractConstraintFormula)constraintValue);
		else {
			Logger.getLogger(TheoremProver.class).fatal("constraint value type \"" + (constraintValue == null ? "null" : constraintValue.getClass().getSimpleName()) + "\" is not supported");
			throw new UnsupportedConstraintValueException(constraintValue);
		}
	}
	
	/**
	 * 
	 * @param singleTheorems
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException
	 */
	protected Theorem getConstraintForArguments(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		List<AbstractConstraint> constraints = new ArrayList<AbstractConstraint>();
		List<VariableField> variableFields = new ArrayList<VariableField>();
		Map<String, ParameterObject> variablesMap = new HashMap<String, ParameterObject>();
		
		List<PrefixedField> prefixedFieldsList = new ArrayList<PrefixedField>();
		
		for(AbstractSingleTheorem singleTheorem : singleTheorems) {
			AbstractConstraint constraint = singleTheorem.constraint;
			
			for(PrefixedField prefixedField : constraint.prefixedFields) {
				if(prefixedField.fieldCode == Opcode.aload_0 && !prefixedField.isVariable && constraint.matches(prefixedField.prefixedName))
					constraint.replaceAll(prefixedField, getAttributeReplacement(prefixedField));
				else if(prefixedField.fieldCode == Opcode.aload && constraint.matches(prefixedField))
					if(!prefixedFieldsList.contains(prefixedField))
						prefixedFieldsList.add(prefixedField);
			}
		
			int parameterCount = singleTheorem.fields.length;
			
			ConstraintParameter[] constraintParameters = new ConstraintParameter[parameterCount];
			List<Field>[] parameterFields = singleTheorem.fields;
			for(int i=0; i<parameterCount; i++)
				constraintParameters[i] = new ConstraintParameter(component, i, parameterFields[i]);
			
			boolean skipTheorem = false;
			for(ConstraintParameter constraintParameter : constraintParameters) {
				if(!constraintParameter.isIncrementable()) {
					skipTheorem = true;
					break;
				}
			}
			if(skipTheorem)
				continue;
			
			List<ParameterObject> parameterObjects = new ArrayList<ParameterObject>();
			ParameterObject currentParameterObject = null;
			
			do {
				AbstractConstraint cConstraint = constraint.clone();
				for(PrefixedField prefixedField : prefixedFieldsList) {
					ConstraintParameter currentConstraintParameter = constraintParameters[prefixedField.value-1];
					if(!prefixedField.isVariable) {
						String replacement = getReplacement(prefixedField, currentConstraintParameter.getCurrentCollectionObject());
						cConstraint.replaceAll(prefixedField, replacement);
					} else {
						Object parameterObject = getParameterObject(prefixedField, currentConstraintParameter.getCurrentCollectionObject());
						int index = -1;
						for(ParameterObject paramObject : parameterObjects) {
							if(paramObject.object.equals(parameterObject) && paramObject.prefixedField.field.equals(prefixedField.field)) {
								currentParameterObject = paramObject;
								index = currentParameterObject.index;
								break;
							}
						}
						if(index == -1) {
							int maxIndex = 0;
							for(ParameterObject paramObject : parameterObjects)
								if(paramObject.prefixedField.field.equals(prefixedField.field))
									maxIndex = (paramObject.index > maxIndex ? paramObject.index : maxIndex);
							currentParameterObject = new ParameterObject(parameterObject, prefixedField, maxIndex+1);
							parameterObjects.add(currentParameterObject);
							index = currentParameterObject.index;
						}
						String prefixedVariableName = prefixedField.prefieldsPrefixedName + "_" + index;
						variablesMap.put(prefixedVariableName, currentParameterObject);
						VariableField variableField = new VariableField(prefixedVariableName, prefixedField.fieldType);
						if(!variableFields.contains(variableField))
							variableFields.add(variableField);
						cConstraint.replaceAll(prefixedField, prefixedVariableName);
					}
				}
				
				AbstractConstraint abstractPartialConstraint = cConstraint.evaluate();
				if(abstractPartialConstraint instanceof AbstractBooleanConstraint) {
					AbstractBooleanConstraint abstractBooleanConstraint = (AbstractBooleanConstraint)abstractPartialConstraint;
					if(!abstractBooleanConstraint.value)
						throw new NotSatisfyableException("one or more of the constraints are not satisfyable for the given instance");
				} else
					constraints.add(abstractPartialConstraint);
			} while(KoselleckUtils.incrementIndices(constraintParameters));
		}
		
		return new Theorem(variablesMap, constraints, variableFields);
	}
	
	/** public methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param component
	 */
	public void setComponent(Object component) {
		this.component = component;
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	private String getAttributeReplacement(PrefixedField prefixedField) {
		if(prefixedField.fieldCode != Opcode.aload_0) {
			Logger.getLogger(TheoremProver.class).fatal("given field \"" + prefixedField.field.getName() + "\" is no attribute field");
			throw new IllegalArgumentException("given field \"" + prefixedField.field.getName() + "\" is no attribute field");
		}
		
		return getReplacement(prefixedField, component);
	}
	
	/**
	 * 
	 * @param prefixedField
	 * @param startingObject
	 * 
	 * @return
	 */
	private Object getParameterObject(PrefixedField prefixedField, Object startingObject) {
		Object parameterObject = startingObject;
		for(PrefixedField prePrefixedField : prefixedField.preFields) {
			prePrefixedField.field.setAccessible(true);
			try {
				parameterObject = prePrefixedField.field.get(parameterObject);
			} catch (IllegalArgumentException | IllegalAccessException e) {
				Logger.getLogger(TheoremProver.class).fatal("could not access field \"" + prePrefixedField.field.getName() +"\"");
				throw new IllegalArgumentException("could not access field \"" + prePrefixedField.field.getName() +"\"");
			}
		}
		
		return parameterObject;
	}
	
	/**
	 * 
	 * @param prefixedField
	 * @param startingObject
	 * 
	 * @return
	 */
	private String getReplacement(PrefixedField prefixedField, Object startingObject) {
		Object replacement = startingObject;
		for(PrefixedField prePrefixedField : prefixedField.preFields) {
			prePrefixedField.field.setAccessible(true);
			try {
				replacement = prePrefixedField.field.get(replacement);
			} catch (IllegalArgumentException | IllegalAccessException e) {
				Logger.getLogger(TheoremProver.class).fatal("could not access field \"" + prePrefixedField.field.getName() +"\"");
				throw new IllegalArgumentException("could not access field \"" + prePrefixedField.field.getName() +"\"");
			}
		}
		prefixedField.field.setAccessible(true);
		try{
			replacement = prefixedField.field.get(replacement);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			Logger.getLogger(TheoremProver.class).fatal("could not access field \"" + prefixedField.field.getName() +"\"");
			throw new IllegalArgumentException("could not access field \"" + prefixedField.field.getName() +"\"");
		}
		
		return replacement.toString();
	}
}
