package de.agra.fomeja;

/* imports */
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.fomeja.annotations.Variable;
import de.agra.fomeja.backends.Prover;
import de.agra.fomeja.backends.datatypes.Constraint;
import de.agra.fomeja.backends.datatypes.ResultModel;
import de.agra.fomeja.backends.parameterobjects.ParameterObject;
import de.agra.fomeja.datatypes.PreField;
import de.agra.fomeja.datatypes.PreFieldList;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.agra.fomeja.exceptions.ModelException;
import de.agra.fomeja.exceptions.SatisfyException;
import de.agra.fomeja.types.BooleanConnector;
import de.agra.fomeja.types.CompareOperator;
import de.agra.fomeja.utils.ClassUtils;
import de.agra.fomeja.utils.ExpressionUtils;
import de.agra.fomeja.utils.FomejaUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 *
 * @param <T>
 */
public class FomejaModel<T> {
	/** COMMENT */
	private Class<T> cls;

	/** instance of the theorem prover to use */
	private Prover<?> prover;

	/** COMMENT */
	private Constraint constraint;

	/** COMMENT */
	private List<BoolExpression> prevResultExprs;

	/** COMMENT */
	private int modelC;

	/**
	 * COMMENT
	 * 
	 * @param cls
	 */
	public FomejaModel(Class<T> cls) {
		this.cls = cls;

		this.prover = FomejaDefaults.getDefaultProver();
		this.constraint = this.getConstraint();

		this.prevResultExprs = new ArrayList<BoolExpression>();

		this.modelC = 0;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public T getNext() {
		T modelObj;
		try {
			modelObj = this.cls.newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			String message = "test object class needs to have a constructor with no parameters: " + e.getMessage();
			Logger.getLogger(FomejaModel.class).fatal(message);
			throw new ModelException(message);
		}

		try {
			this.assignConcreteInstance(modelObj, this.prover.solveNext(this.getNextExprs()));
		} catch (SatisfyException e) {
			if (this.modelC > 0) {
				Logger.getLogger(FomejaModel.class).warn("could not generate next model object; stopped at model '" + (this.modelC+1) + "'");
				return null;
			} else {
				String message = "the theorem is not satisfiable: " + e.getMessage();
				Logger.getLogger(FomejaModel.class).error(message);
				throw new ModelException(message);
			}
		}

		++this.modelC;

		return modelObj;
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	private List<BoolExpression> getNextExprs() throws SatisfyException {
		if (this.modelC == 0)
			return this.constraint.getConstraintExprs();
		else if (!this.prevResultExprs.isEmpty()) {
			List<BoolExpression> lastPrevExprList = new ArrayList<BoolExpression>();
			lastPrevExprList.add(this.prevResultExprs.get(this.prevResultExprs.size()-1));
			return lastPrevExprList;
		} else {
			String message = "no previous result for model #" + this.modelC + " given";
			Logger.getLogger(FomejaModel.class).fatal(message);
			throw new SatisfyException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param modelObj
	 * @param resultModel
	 */
	private void assignConcreteInstance(T modelObj, ResultModel resultModel) {
		ConnectedBoolExpr boolExpr = new ConnectedBoolExpr(BooleanConnector.OR);

		this.prover.clearExtraExprs();

		for (ParameterObject paramObj : this.constraint.getParameterObjects()) {
			Object proverResult = resultModel.getOrDefault(paramObj.getName(), paramObj.getPreFieldList().last().getField().getType());
			if (proverResult == null) {
				String message = "can neither assign result of model nor default value for variable \"" + paramObj + "\"";
				Logger.getLogger(FomejaModel.class).fatal(message);
				throw new ModelException(message);
			}

			Variable paramVar = paramObj.getPreFieldList().last().getField().getAnnotation(Variable.class);
			if (paramVar != null && paramVar.alter() > 0 && this.modelC+1%paramVar.alter() == 0)
				this.prover.addExtraExpr(this.getNegExpr(paramObj.getName(), proverResult));

			this.setFieldValue(this.getFieldValue(modelObj, paramObj.getPreFieldList().head(-1)),
					paramObj.getPreFieldList().last().getField(), proverResult);

			boolExpr.add(this.getNegExpr(paramObj.getName(), proverResult));
		}

		if (!boolExpr.isEmpty())
			this.prevResultExprs.add(boolExpr);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param resultObj
	 * 
	 * @return
	 */
	private BoolExpression getNegExpr(String name, Object resultObj) {
		if (resultObj instanceof String) {
			ConnectedBoolExpr boolExpr = new ConnectedBoolExpr(BooleanConnector.OR);
			char[] chars = ((String) resultObj).toCharArray();
			for (int i=0; i<chars.length; i++)
				boolExpr.add(ExpressionUtils.getCompareExpr("string-" + name + "-c" + i, CompareOperator.NOT_EQUAL, (int) chars[i]));
			boolExpr.add(ExpressionUtils.getCompareExpr("string-" + name + "-c" + chars.length, CompareOperator.GREATER_EQUAL, 0));
			return boolExpr;
		} else
			return ExpressionUtils.getCompareExpr(name, CompareOperator.NOT_EQUAL, resultObj);
	}

	/**
	 * COMMENT
	 * 
	 * @param modelObj
	 * @param preFieldList
	 * 
	 * @return
	 */
	private Object getFieldValue(T modelObj, PreFieldList preFieldList) {
		Object object = modelObj;
		boolean isVariable = false;
		for (PreField preField : preFieldList) {
			isVariable = isVariable || preField.isVariable();
			object = this.getFieldValue(object, preField.getField(), isVariable);
		}

		return object;
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param field
	 * @param isVariable
	 * 
	 * @return
	 */
	private Object getFieldValue(Object object, Field field, boolean isVariable) {
		boolean accessibility = field.isAccessible();
		field.setAccessible(true);
		try {
			Object obj;
			if (isVariable && (obj = field.get(object)) == null) {
				obj = this.getNewInstanceForType(field.getType(), new HashSet<Class<?>>());
				field.set(object, obj);
				return obj;
			} else
				return field.get(object);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			String message = "could not access field \"" + field.getName() + "\" on object \"" + object + "\": " + e.getMessage();
			Logger.getLogger(FomejaModel.class).fatal(message);
			throw new ModelException(message);
		} catch (InstantiationException | InvocationTargetException e) {
			String message = "could not instantiate object of type \"" + field.getType().getSimpleName() + "\" on field \"" + field.getName() + "\" on object \"" + object + "\": " + e.getMessage();
			Logger.getLogger(FomejaModel.class).fatal(message);
			throw new ModelException(message);
		} finally {
			field.setAccessible(accessibility);
		}
	}

	/**
	 * COMMENT
	 * 
	 * TODO handle interfaces
	 * 
	 * @param type
	 * @param visitedTypes
	 * 
	 * @return
	 * 
	 * @throws InstantiationException 
	 * @throws InvocationTargetException 
	 * @throws IllegalArgumentException 
	 * @throws IllegalAccessException 
	 */
	private Object getNewInstanceForType(Class<?> type, Set<Class<?>> visitedTypes) throws InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		/* check for recursive types */
		if (visitedTypes.contains(type))
			return null;
		else {
			visitedTypes = new HashSet<Class<?>>(visitedTypes);
			visitedTypes.add(type);
		}

		/* handle primitive types */
		if (ClassUtils.isPrimitiveType(type))
			return FomejaDefaults.getDefaultForPrimitiveType(type);
		else if (type.isEnum())
			return type.getEnumConstants()[(int) FomejaDefaults.getDefaultForPrimitiveType(type)];

		Constructor<?> constructor = null;
		/* get constructor with minimum parameters */
		for (Constructor<?> declConstr : type.getDeclaredConstructors())
			if (constructor == null || (
					declConstr.isAccessible() && // TODO use unaccessible constructors (private ones) too?
					declConstr.getParameterTypes().length < constructor.getParameterTypes().length))
				constructor = declConstr;

		/* check if type has constructor since interfaces do not have any constructors */
		if (constructor == null) // TODO what to do with interfaces?
			throw new InstantiationException("type \"" + type.getSimpleName() + "\" has no constructor (maybe interface?)");

		Object[] constructorParams = new Object[constructor.getParameterTypes().length];
		for (int i=0; i<constructor.getParameterTypes().length; i++)
			constructorParams[i] = this.getNewInstanceForType(constructor.getParameterTypes()[i], visitedTypes);

		return constructor.newInstance(constructorParams);
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param field
	 * @param value
	 * 
	 * @return
	 */
	private void setFieldValue(Object object, Field field, Object value) {
		boolean accessibility = field.isAccessible();
		field.setAccessible(true);
		try {
			if (ClassUtils.isBooleanType(field.getType())
					&& ClassUtils.isIntegerType(value.getClass()))
				value = (((Integer) value) == 0 ? false : true);
			field.set(object, value);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			String message = "could not access field \"" + field.getName() + "\" on object \"" + object + "\"";
			Logger.getLogger(FomejaModel.class).fatal(message);
			throw new IllegalArgumentException(message + "\n" + e.getMessage());
		} finally {
			field.setAccessible(accessibility);
		}
	}

	/**
	 * COMMENT
	 */
	private Constraint getConstraint() {
		try {
			return FomejaUtils.getConstraintForComponent(this.cls.newInstance());
		} catch (InstantiationException | IllegalAccessException e) {
			String message = "could not instantiate new object of type \"" + this.cls.getSimpleName() + "\": " + e.getMessage();
			Logger.getLogger(FomejaModel.class).fatal(message);
			throw new ModelException(message);
		}
	}
}
