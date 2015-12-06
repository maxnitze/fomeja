package de.agra.fomeja.decompiling.expressions.atomar;

/* imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.fomeja.annotations.Variable;
import de.agra.fomeja.datatypes.PreField;
import de.agra.fomeja.datatypes.PreFieldList;
import de.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.misc.ComponentVariables;
import de.agra.fomeja.exceptions.ExpressionException;
import de.agra.fomeja.exceptions.NotConvertibleException;
import de.agra.fomeja.types.ArithmeticOperator;
import de.agra.fomeja.utils.ClassUtils;
import de.agra.fomeja.utils.ExpressionUtils;

/**
 * AbstractConstraintLiteral represents a literal in a constraint value.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AtomExpr<T> extends Expression implements Comparable<AtomExpr<?>> {
	/** the value of the literal */
	private T value;

	/** COMMENT */
	private Object replacedValue;

	/** the name of the value */
	private String name;

	/** COMMENT */
	private Field field;

	/** flag if the value is variable */
	private boolean isVariable;

	/** flag that indicates if the value is a number type */
	private boolean isNumberType;

	/** flag that indicates if the value is a finished type */
	private boolean isFinishedType;

	/**
	 * Constructor for a new atomar expression.
	 * 
	 * @param value the new value for the literal
	 */
	public AtomExpr(T value) {
		super(value, new ArrayList<PreField>());
		this.value = value;

		this.isVariable = false;
		this.isFinishedType = true;

		this.field = null;
		if (value != null) {
			this.name = value.getClass().getSimpleName() + "@" + Integer.toHexString(value.hashCode());
			this.isNumberType = ClassUtils.isBasicNumberType(value.getClass());
		} else {
			this.name = "";
			this.isNumberType = false;
		}
	}

	/**
	 * Constructor for a new atomar expression.
	 * 
	 * @param field COMMENT
	 * @param preFields COMMENT
	 */
	public AtomExpr(Field field, PreFieldList preFields) {
		super(preFields.getObject(), preFields);
		this.value = null;

		this.field = field;

		if (this.field != null) {
			this.name = this.getPreFieldList().getName() +  "_" + this.field.getName();
			this.isVariable = this.field.getAnnotation(Variable.class) != null;
			this.isNumberType = ClassUtils.isBasicNumberType(field.getType());
		} else {
			this.name = "";
			this.isVariable = true;
			this.isNumberType = false;
		}

		this.isFinishedType = false;
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param isNumberType
	 */
	public AtomExpr(String name, boolean isNumberType) {
		super(-1, new ArrayList<PreField>());
		this.value = null;

		this.field = null;

		this.name = name;

		this.isVariable = true;
		this.isNumberType = isNumberType;
		this.isFinishedType = false;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public T getValue() {
		return this.value;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	Object getReplacedValue() {
		return this.replacedValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param replacedValue
	 */
	void setReplacedValue(Object replacedValue) {
		this.replacedValue = replacedValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Field getField() {
		return this.field;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isVariable() {
		return this.isVariable;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isNumberType() {
		return this.isNumberType;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isFinishedType() {
		return this.isFinishedType;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isFinishedNumberType() {
		return this.isNumberType && this.isFinishedType;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isUnfinishedFieldType() {
		return !this.isFinishedType && this.field != null;
	}

	/** package methods
	 * ----- ----- ----- ----- ----- */

	void setUnfinished() {
		this.isFinishedType = false;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(String regex) {
		if (!this.isFinishedType)
			return this.name.matches(regex);
		else
			return false;
	}

	@Override
	public void replaceAll(String regex, Object replacement) {
		if (!this.isFinishedType && this.name.matches(regex)) {
			if (replacement instanceof String) {
				String replacementString = (String) replacement;
				if (replacementString.matches("^\\d+(\\.\\d+)?d$"))
					this.replacedValue = Double.parseDouble(replacementString);
				else if (replacementString.matches("^\\d+(\\.\\d+)?f$"))
					this.replacedValue = Float.parseFloat(replacementString);
				else if (replacementString.matches("^\\d+$"))
					this.replacedValue = Integer.parseInt(replacementString);
				else
					this.name = (String) replacement;
			} else
				this.replacedValue = replacement;
		}
	}

	@Override
	public Expression substitude(Map<String, Expression> exprs) {
		Expression expr = exprs.get(this.getName());
		if (!this.isFinishedType && expr != null && !expr.equals(this))
			return expr.substitude(exprs);
		else
			return this;
	}

	@Override
	public AtomExpr<?> evaluate(ComponentVariables compVars) {
		if (!this.isFinishedType && this.replacedValue != null)
			return ExpressionUtils.getAtomExprFromObject(this.replacedValue);
		else
			return this;
	}

	@Override
	public AtomExpr<?> simplify() {
		return this;
	}

	@Override
	public boolean isBoolExpr() {
		return false;
	}

	@Override
	public BoolExpression toBoolExpr() {
		String message = "can not convert atomar expression \"" + this + "\" to bool expression";
		Logger.getLogger(AtomExpr.class).fatal(message);
		throw new NotConvertibleException(message);
	}

	@Override
	public boolean isUnfinished() {
		return !this.isFinishedType();
	}

	/** overridden atomar expr methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Set<AtomExpr<?>> getRequiredAtomExprs(boolean isRequired, ComponentVariables compVars) {
		Set<AtomExpr<?>> requiredAtomExprs = new HashSet<AtomExpr<?>>();
		if (isRequired && (this.isVariable || this.getPreFieldList().isVariable()))
			requiredAtomExprs.add(this);
		return requiredAtomExprs;
	}

	@Override
	public boolean hasAtomVoidExprs() {
		return false;
	}

	@Override
	public Set<AtomVoidExpr> getAtomVoidExprs() {
		return new HashSet<AtomVoidExpr>();
	}

	@Override
	public boolean hasAtomStringExprs() {
		return false;
	}

	@Override
	public boolean hasStraightPreparableAtomStringExprs() {
		return false;
	}

	@Override
	public Set<AtomStringExpr> getAtomStringExprs() {
		return new HashSet<AtomStringExpr>();
	}

	/** overridden object methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AtomExpr<?>))
			return false;

		AtomExpr<?> atomExpr = (AtomExpr<?>) object;

		if (this.isFinishedType()) {
			if (this.value == null || atomExpr.value == null)
				return this.value == atomExpr.value;
			else
				return this.value.equals(atomExpr.value);
		} else
			return (this.field == null && atomExpr.field == null && this.name.equals(atomExpr.name))
					|| (this.field != null && atomExpr.field != null
							&& this.field.equals(atomExpr.field)
							&& this.name.equals(atomExpr.name)
							&& this.getPreFieldList().equals(atomExpr.getPreFieldList()));
	}

	@Override
	public int compareTo(AtomExpr<?> atomExpr) {
		return ExpressionUtils.compareFinishedAtomExprs(this, atomExpr);
	}

	@Override
	public String toString() {
		return this.isFinishedType ? (this.value != null ? this.printObjectValue(this.value) : "NULL") : (this.replacedValue != null ? this.printObjectValue(this.replacedValue) : this.name);
	}

	/**
	 * COMMENT
	 * 
	 * @param value
	 * 
	 * @return
	 */
	private String printObjectValue(Object value) {
		return value.getClass().isArray() ? Arrays.toString((Object[]) value) : (ClassUtils.isBasicType(value.getClass()) ? value.toString() : (value.getClass().getSimpleName() + "@" + Integer.toHexString(value.hashCode())));
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */
	
	@Override
	public abstract AtomExpr<?> clone();

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param atomExpr
	 * @param operator
	 * 
	 * @return
	 */
	public Expression calc(AtomExpr<?> atomExpr, ArithmeticOperator operator) {
		if (!this.isFinishedNumberType() || !atomExpr.isFinishedNumberType())
			return new ArithmeticExpr(this, operator, atomExpr);
		else if (ClassUtils.isDoubleType(this.getValue().getClass())
				&& ClassUtils.isDoubleType(atomExpr.getValue().getClass()))
			return new AtomDoubleExpr(operator.calc((Double) this.getValue(), (Double) atomExpr.getValue()));
		else if (ClassUtils.isDoubleType(this.getValue().getClass())
				&& ClassUtils.isFloatType(atomExpr.getValue().getClass()))
			return new AtomDoubleExpr(operator.calc((Double) this.getValue(), ((Float) atomExpr.getValue()).doubleValue()));
		else if (ClassUtils.isDoubleType(this.getValue().getClass())
				&& ClassUtils.isIntegerType(atomExpr.getValue().getClass()))
			return new AtomDoubleExpr(operator.calc((Double) this.getValue(), ((Integer) atomExpr.getValue()).doubleValue()));
		else if (ClassUtils.isFloatType(this.getValue().getClass())
				&& ClassUtils.isDoubleType(atomExpr.getValue().getClass()))
			return new AtomDoubleExpr(operator.calc(((Float) this.getValue()).doubleValue(), (Double) atomExpr.getValue()));
		else if (ClassUtils.isFloatType(this.getValue().getClass())
				&& ClassUtils.isFloatType(atomExpr.getValue().getClass()))
			return new AtomFloatExpr(operator.calc((Float) this.getValue(), (Float) atomExpr.getValue()));
		else if (ClassUtils.isFloatType(this.getValue().getClass())
				&& ClassUtils.isIntegerType(atomExpr.getValue().getClass()))
			return new AtomFloatExpr(operator.calc((Float) this.getValue(), ((Integer) atomExpr.getValue()).floatValue()));
		else if (ClassUtils.isIntegerType(this.getValue().getClass())
				&& ClassUtils.isDoubleType(atomExpr.getValue().getClass()))
			return new AtomDoubleExpr(operator.calc(((Integer) this.getValue()).doubleValue(), (Double) atomExpr.getValue()));
		else if (ClassUtils.isIntegerType(this.getValue().getClass())
				&& ClassUtils.isFloatType(atomExpr.getValue().getClass()))
			return new AtomFloatExpr(operator.calc(((Integer) this.getValue()).floatValue(), (Float) atomExpr.getValue()));
		else if (ClassUtils.isIntegerType(this.getValue().getClass())
				&& ClassUtils.isIntegerType(atomExpr.getValue().getClass()))
			return new AtomIntegerExpr(operator.calc((Integer) this.getValue(), (Integer) atomExpr.getValue()));
		else {
			String message = "\"" + this + "\" and \"" + atomExpr + "\" are not calculatable";
			Logger.getLogger(AtomExpr.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreField toPreField() {
		if (!this.isFinishedType)
			return new PreField(this.field);
		else {
			String message = "cannot cast finished atomar expression \"" + this + "\" to prefield";
			Logger.getLogger(AtomExpr.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreFieldList toPreFieldList() {
		PreFieldList preFieldList = this.getPreFieldList().clone();
		preFieldList.add(this.toPreField());
		return preFieldList;
	}
}
