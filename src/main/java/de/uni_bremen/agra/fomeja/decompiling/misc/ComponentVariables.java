package de.uni_bremen.agra.fomeja.decompiling.misc;

/* imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.Dialect;
import de.uni_bremen.agra.fomeja.backends.datatypes.ComponentCollectionList;
import de.uni_bremen.agra.fomeja.backends.parameterobjects.BasicParameterObject;
import de.uni_bremen.agra.fomeja.backends.parameterobjects.EnumParameterObject;
import de.uni_bremen.agra.fomeja.backends.parameterobjects.ObjectParameterObject;
import de.uni_bremen.agra.fomeja.backends.parameterobjects.ParameterObject;
import de.uni_bremen.agra.fomeja.backends.parameterobjects.RangedParameterObject;
import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.exceptions.ExpressionException;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;
import de.uni_bremen.agra.fomeja.types.CompareOperator;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ComponentVariables {
	/** COMMENT */
	private Object component;

	/** COMMENT */
	private Map<String, ParameterObject> variables;

	/**
	 * COMMENT
	 * 
	 * @param component
	 */
	public ComponentVariables(Object component) {
		this.component = component;
		this.variables = new HashMap<String, ParameterObject>();
	}

	/**
	 * COMMENT
	 * 
	 * @param component
	 * @param variables
	 */
	private ComponentVariables(Object component, Map<String, ParameterObject> variables) {
		this.component = component;
		this.variables = variables;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 * 
	 * @return
	 */
	public ParameterObject add(PreFieldList preFieldList) {
		if (this.variables.containsKey(preFieldList.getName()))
			return this.variables.get(preFieldList.getName());
		else
			return this.variables.put(preFieldList.getName(), this.getNewParameterObject(preFieldList));
	}

	/**
	 * OMMENT
	 * 
	 * @param key
	 * 
	 * @return
	 */
	public ParameterObject get(String key) {
		return this.variables.get(key);
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Set<ParameterObject> getParameterObjects() {
		return new HashSet<ParameterObject>(this.variables.values());
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<BoolExpression> getRangeExprs() {
		List<BoolExpression> rangeExprs = new ArrayList<BoolExpression>();
		for (ParameterObject paramObject : this.variables.values())
			if (paramObject.getPreFieldList().last().isVariable() && paramObject instanceof RangedParameterObject)
				rangeExprs.add(new ConnectedBoolExpr(
						BooleanConnector.AND,
						new CompareExpr(new AtomIntegerExpr(paramObject.getName()), CompareOperator.GREATER_EQUAL, new AtomIntegerExpr(0)),
						new CompareExpr(new AtomIntegerExpr(paramObject.getName()), CompareOperator.LESS, new AtomIntegerExpr(((RangedParameterObject) paramObject).getRangeSize()))));
		return rangeExprs;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<BoolExpression> getConnectionExprs() {
		List<BoolExpression> connectionExprs = new ArrayList<BoolExpression>();
		for (ParameterObject paramObject : this.variables.values()) {
			if (!paramObject.getPreFieldList().last().isVariable() && paramObject.isDependend()/* && this.confirmedVariables.contains(paramObject.getName())*/) {
				ConnectedBoolExpr boolExprSet = new ConnectedBoolExpr(BooleanConnector.OR);
				ObjectParameterObject dependentParamObject = paramObject.getDependentParameterObject();
				for (int i=0; i<dependentParamObject.getRangeSize(); i++) {
					CompareExpr paramObjectExpr;
					if (paramObject instanceof BasicParameterObject) {
						if (ClassUtils.isDoubleType(paramObject.getPreFieldList().last().getClass()))
							paramObjectExpr = new CompareExpr(new AtomDoubleExpr(paramObject.getName()), CompareOperator.EQUAL,
									new AtomDoubleExpr((Double) paramObject.getPreFieldList().getFieldValue(dependentParamObject.getPreFieldList().size(), dependentParamObject.getRangeElement(i))));
						else  if (ClassUtils.isFloatType(paramObject.getPreFieldList().last().getClass()))
							paramObjectExpr = new CompareExpr(new AtomFloatExpr(paramObject.getName()), CompareOperator.EQUAL,
									new AtomFloatExpr((Float) paramObject.getPreFieldList().getFieldValue(dependentParamObject.getPreFieldList().size(), dependentParamObject.getRangeElement(i))));
						else if (ClassUtils.isIntegerType(paramObject.getPreFieldList().last().getClass()))
							paramObjectExpr = new CompareExpr(new AtomIntegerExpr(paramObject.getName()), CompareOperator.EQUAL,
									new AtomIntegerExpr((Integer) paramObject.getPreFieldList().getFieldValue(dependentParamObject.getPreFieldList().size(), dependentParamObject.getRangeElement(i))));
						else {
							String message = "cannot create connection expression from basic parameter object that is neither double, float, nor integer";
							Logger.getLogger(ComponentVariables.class).fatal(message);
							throw new ExpressionException(message);
						}
					} else if (paramObject instanceof RangedParameterObject)
						paramObjectExpr = new CompareExpr(
								new AtomIntegerExpr(paramObject.getName()), CompareOperator.EQUAL,
								new AtomIntegerExpr(((RangedParameterObject) paramObject).getObjectMapping(paramObject.getPreFieldList().getFieldValue(dependentParamObject.getPreFieldList().size(), dependentParamObject.getRangeElement(i)))));
					else  {
						String message = "cannot create connection expression from parameterobject that is neither of basic nor ranged type";
						Logger.getLogger(ComponentVariables.class).fatal(message);
						throw new ExpressionException(message);
					}

					boolExprSet.add(new ConnectedBoolExpr(
							BooleanConnector.AND,
							new CompareExpr(new AtomIntegerExpr(dependentParamObject.getName()), CompareOperator.EQUAL, new AtomIntegerExpr(i)), paramObjectExpr));
				}

				if (!boolExprSet.getBoolExprs().isEmpty())
					connectionExprs.add(boolExprSet);
			}
		}

		return connectionExprs;
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 * 
	 * @return
	 */
	private ParameterObject getNewParameterObject(PreFieldList preFieldList) {
		Field field = preFieldList.last().getField();
		if (ClassUtils.isBasicType(field.getType()))
			return new BasicParameterObject(preFieldList, this.getDependentParameterObject(preFieldList));
		else if (field.getType().isEnum()) {
			@SuppressWarnings("unchecked")
			Class<Enum<?>> enumClass = (Class<Enum<?>>) field.getType();
			return new EnumParameterObject(preFieldList, enumClass, this.getDependentParameterObject(preFieldList));
		} else
			return new ObjectParameterObject(preFieldList, this.getComponentCollection(field), this.getDependentParameterObject(preFieldList));
	}

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 * 
	 * @return
	 */
	private ObjectParameterObject getDependentParameterObject(PreFieldList preFieldList) {
		PreFieldList varHead = preFieldList.variableHead();
		if (!varHead.isEmpty() && !preFieldList.isEmpty() && !preFieldList.last().isVariable()) {
			ParameterObject paramObject = this.get(varHead.getName());
			if (paramObject == null)
				paramObject = this.add(varHead);

			if (paramObject instanceof ObjectParameterObject)
				return (ObjectParameterObject) paramObject;
			else {
				String message = "cannot set parameterobject of type \"" + paramObject.getClass().getSimpleName() + "\" to dependent parameter object";
				Logger.getLogger(ComponentVariables.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		} else /* no dependent parameter object */
			return null;
	}

	/**
	 * COMMENT
	 * 
	 * @param literalPreField
	 * 
	 * @return
	 */
	private ComponentCollectionList getComponentCollection(Field field) {
		ComponentCollectionList componentCollections = new ComponentCollectionList();

		/* get list of component-collections for type of field */
		List<Field> collectionFields = RefactoringUtils.getCollectionFields(this.component.getClass(), field.getGenericType());
		for (Field collectionField : collectionFields) {
			boolean accessibility = collectionField.isAccessible();
			collectionField.setAccessible(true);
			try {
				componentCollections.add((Collection<?>) collectionField.get(this.component));
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not get field \"" + collectionField.getName() + "\" for component";
				Logger.getLogger(Dialect.class).error(message);
				throw new IllegalArgumentException(message);
			} finally {
				collectionField.setAccessible(accessibility);
			}
		}

		return componentCollections;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public ComponentVariables clone() {
		return new ComponentVariables(this.component, new HashMap<String, ParameterObject>(this.variables));
	}

	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("unconfirmed variables for component \"" + this.component + "\"");
		for (String variable : this.variables.keySet())
			stringBuilder.append("\n  ")
				.append(variable);

		return stringBuilder.toString();
	}
}
