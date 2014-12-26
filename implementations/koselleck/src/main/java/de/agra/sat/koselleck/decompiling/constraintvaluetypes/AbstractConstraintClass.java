package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintClass extends AbstractConstraintValue {
	/** COMMENT */
	private Class<?> value;

	/**
	 * COMMENT
	 * 
	 * @param value
	 * @param opcode
	 * @param fieldCodeIndex
	 */
	public AbstractConstraintClass(Class<?> value, Opcode opcode, int fieldCodeIndex) {
		super(fieldCodeIndex, opcode);
		this.value = value;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Class<?> getValue() {
		return this.value;
	}

	/** inherited methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {}

	@Override
	public AbstractConstraintValue evaluate() {
		return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		Object constraintArgument = constraintArguments.get(this.getFieldCodeIndex());
		if (constraintArgument == null)
			return this;
		else {
			if (constraintArgument instanceof Integer)
				return new AbstractConstraintLiteralInteger((Integer) constraintArgument);
			else if (constraintArgument instanceof Float)
				return new AbstractConstraintLiteralFloat((Float) constraintArgument);
			else if (constraintArgument instanceof Double)
				return new AbstractConstraintLiteralDouble((Double) constraintArgument);
			else
				return new AbstractConstraintLiteralObject((Object) constraintArgument);
		}
	}

	@Override
	public boolean matches(String regex) {
		return false;
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		return new HashSet<AbstractConstraintLiteral<?>>();
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintClass))
			return false;

		AbstractConstraintClass abstractConstraintClass = (AbstractConstraintClass) object;

		return this.getValue().equals(abstractConstraintClass.getValue())
				&& this.getFieldCodeIndex() == abstractConstraintClass.getFieldCodeIndex()
				&& this.getOpcode() == abstractConstraintClass.getOpcode();
	}

	@Override
	public AbstractConstraintClass clone() {
		return new AbstractConstraintClass(this.getValue(), this.getOpcode(), this.getFieldCodeIndex());
	}

	@Override
	public String toString() {
		return "CLASS_" + this.value.getSimpleName();
	}
}
