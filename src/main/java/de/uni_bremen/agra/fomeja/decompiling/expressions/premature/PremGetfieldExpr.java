package de.uni_bremen.agra.fomeja.decompiling.expressions.premature;

/* imports */
import java.lang.reflect.Field;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.annotations.Variable;
import de.uni_bremen.agra.fomeja.datatypes.PreField;
import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomClassExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomEnumExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PremGetfieldExpr extends PrematureExpr {
	/** COMMENT */
	private Expression expr;
	/** COMMENT */
	private Field field;
	/** COMMENT */
	private boolean isVariable;

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param field COMMENT
	 */
	public PremGetfieldExpr(Expression expr, Field field) {
		this.expr = expr;
		this.field = field;
		this.isVariable = field.getAnnotation(Variable.class) != null;
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Expression getExpr() {
		return this.expr;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Field getField() {
		return this.field;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean isVariable() {
		return this.isVariable;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Class<?> getResultType() {
		return this.field.getType();
	}

	@Override
	public boolean matches(String regex) {
		return this.expr.matches(regex);
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		this.expr.replaceAll(regex, replacement);
	}

	@Override
	public PremGetfieldExpr substitude(Map<String, Expression> exprs) {
		this.expr = this.expr.substitude(exprs);
		return this;
	}

	@Override
	public Expression evaluate(ComponentVariables compVars) {
		this.expr = this.expr.evaluate(compVars);

		if (this.expr instanceof AtomExpr<?> && ((AtomExpr<?>) this.expr).isFinishedType() && !this.isVariable)
			return this.getFieldValue();
		else if (this.expr instanceof AtomExpr<?>) {
			PreFieldList exprPreFieldList;
			if ((this.expr instanceof AtomClassExpr) || ((AtomExpr<?>) this.expr).isFinishedType())
				exprPreFieldList = new PreFieldList(((AtomExpr<?>) this.expr).getValue());
			else
				exprPreFieldList = ((AtomExpr<?>) this.expr).toPreFieldList();

			AtomExpr<?> atomExpr;
			if (ClassUtils.isDoubleType(this.field.getType()))
				atomExpr = new AtomDoubleExpr(this.field, exprPreFieldList);
			else if (ClassUtils.isFloatType(this.field.getType()))
				atomExpr = new AtomFloatExpr(this.field, exprPreFieldList);
			else if (ClassUtils.isIntegerType(this.field.getType()))
				atomExpr = new AtomIntegerExpr(this.field, exprPreFieldList);
			else if (this.field.getType().equals(String.class))
				atomExpr = new AtomStringExpr(this.field, exprPreFieldList);
			else if (this.field.getType().isEnum())
				atomExpr = new AtomEnumExpr(this.field, exprPreFieldList);
			else
				atomExpr = new AtomObjectExpr(this.field, exprPreFieldList);

			this.addParameterObjects(compVars, exprPreFieldList, ((AtomExpr<?>) this.expr).getResultType());

			return atomExpr;
		} else
			return this;
	}

	@Override
	public Expression simplify() {
		this.expr = this.expr.simplify();
		if (this.expr instanceof AtomExpr<?> && ((AtomExpr<?>) this.expr).isFinishedType() && !this.isVariable)
			return this.getFieldValue();
		else
			return this;
	}

	/* overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		if (isRequired) {
			Expression evalExpr = this.clone().evaluate(compVars);
			if (evalExpr instanceof AtomExpr<?>)
				requiredAtomExprs.add((AtomExpr<?>) evalExpr);
		}

		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return this.expr.hasAtomVoidExprs();
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		return this.expr.getAtomVoidExprs();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return this.expr.hasAtomStringExprs();
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return this.expr.getAtomStringExprs();
	}

	/* overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PremGetfieldExpr))
			return false;

		PremGetfieldExpr premGFExpr = (PremGetfieldExpr) object;

		return super.equals(premGFExpr)
				&& this.expr.equals(premGFExpr.expr)
				&& this.field.equals(premGFExpr.field);
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(3, 107)
				.appendSuper(super.hashCode())
				.append(this.expr)
				.append(this.field)
				.toHashCode();
	}

	@Override
	public Expression clone() {
		return new PremGetfieldExpr(this.expr.clone(), this.field);
	}

	@Override
	public String toString() {
		return "\"" + this.expr.toString() + "\"." + field.getName();
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomExpr<?> getFieldValue() {
		if (this.expr instanceof AtomExpr<?> && ((AtomExpr<?>) this.expr).isFinishedType() && !this.isVariable) {
			boolean accessibility = this.field.isAccessible();
			this.field.setAccessible(true);
	
			Object value;
			try {
				value = this.field.get(((AtomExpr<?>) this.expr).getValue());
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not get field \"" + this.field.getName() + "\" for value \"" + this.expr + "\"";
				Logger.getLogger(PremGetfieldExpr.class).fatal(message);
				throw new EvaluationException(message);
			} finally {
				this.field.setAccessible(accessibility);
			}
	
			if (ClassUtils.isDoubleType(this.field.getType()))
				return new AtomDoubleExpr((Double) value);
			else if (ClassUtils.isFloatType(this.field.getType()))
				return new AtomFloatExpr((Float) value);
			else if (ClassUtils.isIntegerType(this.field.getType()))
				return new AtomIntegerExpr((Integer) value);
			else if (this.field.getType().equals(String.class))
				return new AtomStringExpr((String) value);
			else if (this.field.getType().isEnum())
				return new AtomIntegerExpr(((Enum<?>) value).ordinal());
			else if (this.field.getType().isArray())
				return this.getArrayFieldValue(value);
			else
				return new AtomObjectExpr(value);
		} else {
			String message = "can not get field \"" + this.field.getName() + "\" from non-finished expression \"" + this.expr + "\"";
			Logger.getLogger(PremGetfieldExpr.class).fatal(message);
			throw new EvaluationException(message);
			
		}
	}

	/**
	 * COMMENT
	 * 
	 * TODO implement support for byte (and maybe long and short apart from
	 *  int?)
	 * 
	 * @param valueArray COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomArrayExpr<?> getArrayFieldValue(Object valueArray) {
		if (this.field.getType().isArray()) {
			if (valueArray instanceof boolean[]) {
				boolean[] boolValueArray = (boolean[]) valueArray;
				AtomArrayExpr<Boolean> atomArrayExpr = new AtomArrayExpr<Boolean>(Boolean.class, boolValueArray.length);
				for (int i=0; i<boolValueArray.length; i++)
					atomArrayExpr.set(i, new AtomBoolExpr(boolValueArray[i]));
				return atomArrayExpr;
			} else if (valueArray instanceof byte[]) {
				String message = "can not get elements from array field of type \"byte[]\" (not implemented yet)";
				Logger.getLogger(PremGetfieldExpr.class).fatal(message);
				throw new EvaluationException(message);
			} else if (valueArray instanceof char[]) {
				char[] charValueArray = (char[]) valueArray;
				AtomArrayExpr<Character> atomArrayExpr = new AtomArrayExpr<Character>(Character.class, charValueArray.length);
				for (int i=0; i<charValueArray.length; i++)
					atomArrayExpr.set(i, new AtomCharacterExpr(charValueArray[i]));
				return atomArrayExpr;
			} else if (valueArray instanceof double[]) {
				double[] doubleValueArray = (double[]) valueArray;
				AtomArrayExpr<Double> atomArrayExpr = new AtomArrayExpr<Double>(Double.class, doubleValueArray.length);
				for (int i=0; i<doubleValueArray.length; i++)
					atomArrayExpr.set(i, new AtomDoubleExpr(doubleValueArray[i]));
				return atomArrayExpr;
			} else if (valueArray instanceof float[]) {
				float[] floatValueArray = (float[]) valueArray;
				AtomArrayExpr<Float> atomArrayExpr = new AtomArrayExpr<Float>(Float.class, floatValueArray.length);
				for (int i=0; i<floatValueArray.length; i++)
					atomArrayExpr.set(i, new AtomFloatExpr(floatValueArray[i]));
				return atomArrayExpr;
			} else if (valueArray instanceof int[]) {
				int[] intValueArray = (int[]) valueArray;
				AtomArrayExpr<Integer> atomArrayExpr = new AtomArrayExpr<Integer>(Integer.class, intValueArray.length);
				for (int i=0; i<intValueArray.length; i++)
					atomArrayExpr.set(i, new AtomIntegerExpr(intValueArray[i]));
				return atomArrayExpr;
			} else if (valueArray instanceof long[]) {
				long[] longValueArray = (long[]) valueArray;
				AtomArrayExpr<Integer> atomArrayExpr = new AtomArrayExpr<Integer>(Integer.class, longValueArray.length);
				for (int i=0; i<longValueArray.length; i++)
					atomArrayExpr.set(i, new AtomIntegerExpr((int) longValueArray[i]));
				return atomArrayExpr;
			} else if (valueArray instanceof short[]) {
				short[] shortValueArray = (short[]) valueArray;
				AtomArrayExpr<Integer> atomArrayExpr = new AtomArrayExpr<Integer>(Integer.class, shortValueArray.length);
				for (int i=0; i<shortValueArray.length; i++)
					atomArrayExpr.set(i, new AtomIntegerExpr((int) shortValueArray[i]));
				return atomArrayExpr;
			} else {
				Object[] objectValueArray = (Object[]) valueArray;
				AtomArrayExpr<Object> atomArrayExpr = new AtomArrayExpr<Object>(Object.class, objectValueArray.length);
				for (int i=0; i<objectValueArray.length; i++)
					atomArrayExpr.set(i, new AtomObjectExpr(objectValueArray[i]));
				return atomArrayExpr;
			}
		} else {
			String message = "can not get array value for field \"" + this.field.getName() + "\" from expression \"" + this.expr + "\"";
			Logger.getLogger(PremGetfieldExpr.class).fatal(message);
			throw new EvaluationException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param compVars COMMENT
	 * @param preFieldList COMMENT
	 * @param exprResultType COMMENT
	 */
	private void addParameterObjects(ComponentVariables compVars, PreFieldList preFieldList, Class<?> exprResultType) {
		for (Field field : exprResultType.getDeclaredFields())
			if (field.getAnnotation(Variable.class) != null)
				compVars.add(this.getThisPrefieldList(preFieldList, field));

		if (this.field.getAnnotation(Variable.class) == null)
			compVars.add(this.getThisPrefieldList(preFieldList, this.field));
	}

	/**
	 * COMMENT
	 * 
	 * @param preFieldList COMMENT
	 * @param field COMMENT
	 * 
	 * @return COMMENT
	 */
	private PreFieldList getThisPrefieldList(PreFieldList preFieldList, Field field) {
		PreFieldList thisPreFieldList = preFieldList.clone();
		thisPreFieldList.add(new PreField(field));
		return thisPreFieldList;
	}
}
