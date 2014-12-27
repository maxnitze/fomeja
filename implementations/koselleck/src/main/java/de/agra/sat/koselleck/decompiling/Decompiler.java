package de.agra.sat.koselleck.decompiling;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintClass;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralDouble;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralEnum;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralFloat;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractPrematureConstraintValueAccessibleObject;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractPrematureConstraintValueConstraint;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineConstantTableAccessibleObject;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineConstantTableClass;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineOffset;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineTableswitch;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineValue;
import de.agra.sat.koselleck.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.sat.koselleck.exceptions.DecompilerException;
import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;
import de.agra.sat.koselleck.exceptions.UnknownOpcodeException;
import de.agra.sat.koselleck.exceptions.UnknownSwitchCaseException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintLiteralException;
import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.types.Opcode;
import de.agra.sat.koselleck.utils.ClassUtils;
import de.agra.sat.koselleck.utils.ConstraintUtils;
import de.agra.sat.koselleck.utils.KoselleckUtils;

/**
 * Decompiler implements a decompiler for java byte code.
 * 
 * @author Max Nitze
 */
public class Decompiler {
	/** stack to process on */
	private final Stack<AbstractConstraintValue> stack;
	/** store to store values */
	private final Map<Integer, AbstractConstraintValue> store;

	/**
	 * Private constructor for a new Decompiler.
	 */
	private Decompiler() {
		this.stack = new Stack<AbstractConstraintValue>();
		this.store = new HashMap<Integer, AbstractConstraintValue>();
	}

	/**
	 * decompile clears the stack and store and then returns the abstract
	 *  constraint starting at index zero of the byte code lines.
	 * 
	 * @param method the method to decompile
	 * @param invokationValue
	 * @param bytecodeLines the byte code lines of the method to decompile
	 * @param argumentValues the method parameters
	 * 
	 * @return the abstract constraint starting at index 0 of the byte code
	 *  lines
	 */
	private AbstractConstraint decompile(Method method, Map<Integer, BytecodeLine> bytecodeLines, AbstractConstraintValue invokationValue, AbstractConstraintValue... argumentValues) {
		this.stack.clear();
		this.store.clear();

		this.store.put(0, invokationValue);

		for (int i=0; i<argumentValues.length; i++)
			this.store.put(i+1, argumentValues[i]);

		return this.parseMethodBytecode(bytecodeLines, 0);
	}

	/** static methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * decompile instantiates a new decompiler with the given disassembled
	 *  method and returns the decompiled abstract constraint.
	 * 
	 * @param disassembledMethod the disassembled method to decompile
	 * @param invokationValue
	 * @param argumentValues the initial elements on the stack
	 * 
	 * @return the decompiled abstract constraint of the disassembled method
	 */
	public static AbstractConstraint decompile(DisassembledMethod disassembledMethod, AbstractConstraintValue invokationValue, AbstractConstraintValue... argumentValues) {
		return new Decompiler().decompile(
				disassembledMethod.getMethod(), disassembledMethod.getBytecodeLines(), invokationValue, argumentValues);
	}

	/** constraint value methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * parseBytecode returns the constraint starting at the given index of the
	 *  map of byte code lines. Recursively every single constraint is added to
	 *  the abstract constraint.
	 * 
	 * @param bytecodeLines the byte code lines to process
	 * @param offset the offset of the byte code line to start from
	 * 
	 * @return the abstract constraint starting at the given index
	 */
	private AbstractConstraint parseMethodBytecode(Map<Integer, BytecodeLine> bytecodeLines, int offset) {
		BytecodeLine bytecodeLine = bytecodeLines.get(offset);
		if (bytecodeLine == null)
			return new AbstractBooleanConstraint(false, null);

		int nextOffset;

		BytecodeLineValue bytecodeLineValue = null;
		BytecodeLineOffset bytecodeLineOffset = null;
		BytecodeLineConstantTableClass bytecodeLineConstantTableClass = null;
		BytecodeLineConstantTableAccessibleObject bytecodeLineConstantTableAccessibleObject = null;
		BytecodeLineTableswitch bytecodeLineTableswitch = null;

		List<PreField> preFields = new ArrayList<PreField>();

		AbstractConstraintValue constraintValue = null;
		AbstractConstraintLiteral<?> constraintLiteral = null;
		AbstractConstraintValue constraintValue1 = null;
		AbstractConstraintValue constraintValue2 = null;
		AbstractConstraintLiteral<?> constraintLiteral1 = null;
		AbstractConstraintLiteral<?> constraintLiteral2 = null;

		AbstractConstraintValue returnValue = null;

		ConstraintOperator constraintOperator = null;

		do {
			nextOffset = bytecodeLine.getFollowingLineNumber();

			switch(bytecodeLine.getOpcode()) {
			case Xload_:
			case Xload:
				this.stack.push(this.store.get(((BytecodeLineValue) bytecodeLine).getValue()));
				break;

			case Xstore_:
			case Xstore:
				this.store.put((Integer)((BytecodeLineValue) bytecodeLine).getValue(), this.stack.pop());
				break;

			case Xconst:
			case Xconst_:
			case bipush:
				this.stack.push(
						new AbstractConstraintLiteralInteger((Integer) ((BytecodeLineValue) bytecodeLine).getValue()));
				break;

			case getfield:
			case getstatic:
				bytecodeLineConstantTableAccessibleObject = (BytecodeLineConstantTableAccessibleObject) bytecodeLine;

				constraintValue = this.stack.pop();
				if (!(constraintValue instanceof AbstractConstraintLiteral<?> || constraintValue instanceof AbstractConstraintClass)) {
					String message = "could not get " + (bytecodeLine.getOpcode() == Opcode.getstatic ? "static " : "") + "field from constraint value \"" + constraintValue + "\" with accessible object \"" + bytecodeLineConstantTableAccessibleObject.getAccessibleObject() + "\"";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}

				if (bytecodeLine.getOpcode() == Opcode.getfield)
					this.stack.push(
							this.getFieldValue(bytecodeLineConstantTableAccessibleObject, constraintValue));
				else
					this.stack.push(
							this.getStaticFieldValue(bytecodeLineConstantTableAccessibleObject, constraintValue));

				break;

			case checkcast:
				constraintValue = this.stack.pop();
				if (!(constraintValue instanceof AbstractConstraintLiteral<?>)) {
					String message = "could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new ClassCastException(message);
				}

				Object constraintValueObject = ((AbstractConstraintLiteral<?>) constraintValue).getValue();
				if (!constraintValueObject.getClass().isAssignableFrom(((BytecodeLineConstantTableClass) bytecodeLine).getClazz())) {
					String message = "could not cast from \"" + constraintValueObject.getClass().getSimpleName() + "\" to \"" + ((BytecodeLineConstantTableClass)bytecodeLine).getClazz().getSimpleName() + "\"";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new ClassCastException(message);
				}
				break;

			case i2d:
				constraintValue = this.stack.pop();

				/** check for abstract constraint literal */
				if (constraintValue instanceof AbstractConstraintLiteral<?>) {
					constraintLiteral = (AbstractConstraintLiteral<?>)constraintValue;

					/** check for integer */
					if (constraintLiteral instanceof AbstractConstraintLiteralInteger) {
						/** push corresponding double to stack */
						this.stack.push(
								new AbstractConstraintLiteralDouble(new Double((Integer) constraintLiteral.getValue())));
					} else if (constraintLiteral.isNumberType()) {
						String message = "could not cast constraint value \"" + constraintLiteral.getValue() + "\" (" + constraintLiteral.getValue().getClass().getSimpleName() + ") to integer";
						Logger.getLogger(Decompiler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					} else
						this.stack.push(constraintLiteral);
				} else
					this.stack.push(constraintValue);

				break;
			case i2f:
				constraintValue = this.stack.pop();

				/** check for abstract constraint literal */
				if (constraintValue instanceof AbstractConstraintLiteral<?>) {
					constraintLiteral = (AbstractConstraintLiteral<?>)constraintValue;

					/** check for integer */
					if (constraintLiteral instanceof AbstractConstraintLiteralInteger) {
						/** push corresponding float to stack */
						this.stack.push(
								new AbstractConstraintLiteralFloat(new Float((Integer) constraintLiteral.getValue())));
					} else if (constraintLiteral.isNumberType()) {
						String message = "could not cast constraint value \"" + constraintLiteral.getValue() + "\" (" + constraintLiteral.getValue().getClass().getSimpleName() + ") to integer";
						Logger.getLogger(Decompiler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					} else
						this.stack.push(constraintLiteral);
				} else
					this.stack.push(constraintValue);

				break;
			case f2d:
				constraintValue = this.stack.pop();

				/** check for abstract constraint literal */
				if (constraintValue instanceof AbstractConstraintLiteral<?>) {
					constraintLiteral = (AbstractConstraintLiteral<?>)constraintValue;

					/** check for float */
					if (constraintLiteral instanceof AbstractConstraintLiteralFloat) {
						/** push corresponding double to stack */
						this.stack.push(
								new AbstractConstraintLiteralDouble(new Double((Float) constraintLiteral.getValue())));
					} else if (constraintLiteral.isNumberType()) {
						String message = "could not cast constraint value \"" + constraintLiteral.getValue() + "\" (" + constraintLiteral.getValue().getClass().getSimpleName() + ") to integer";
						Logger.getLogger(Decompiler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					} else
						this.stack.push(constraintLiteral);
				} else
					this.stack.push(constraintValue);

				break;

			case ldc:
			case ldc2_w:
				bytecodeLineValue = (BytecodeLineValue) bytecodeLine;

				if (ClassUtils.isDoubleClass(bytecodeLineValue.getValue().getClass()))
					this.stack.push(new AbstractConstraintLiteralDouble((Double) bytecodeLineValue.getValue()));
				else if (ClassUtils.isFloatClass(bytecodeLineValue.getValue().getClass()))
					this.stack.push(new AbstractConstraintLiteralFloat((Float) bytecodeLineValue.getValue()));
				else if (ClassUtils.isIntegerClass(bytecodeLineValue.getValue().getClass()))
					this.stack.push(new AbstractConstraintLiteralInteger((Integer) bytecodeLineValue.getValue()));
				else
					this.stack.push(new AbstractConstraintLiteralObject(bytecodeLineValue.getValue()));

				break;

			case Xadd:
			case Xsub:
			case Xmul:
			case Xdiv:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				this.stack.push(this.getCalculatedValue(
						constraintValue1, ArithmeticOperator.fromOpcode(bytecodeLine.getOpcode()), constraintValue2));
				break;

			case _new:
				bytecodeLineConstantTableClass = (BytecodeLineConstantTableClass) bytecodeLine;
				this.stack.push(
						new AbstractConstraintClass(bytecodeLineConstantTableClass.getClazz(), Opcode._new, -1));
				break;

			case invokestatic:
			case invokevirtual:
			case invokespecial:
				bytecodeLineConstantTableAccessibleObject = (BytecodeLineConstantTableAccessibleObject) bytecodeLine;

				/** get arguments for method or constructor */
				ArgumentList argumentValues = this.getArgumentList(bytecodeLineConstantTableAccessibleObject.getAccessibleObject());

				/** pop value from stack */
				constraintValue = this.stack.pop();
				if (bytecodeLine.getOpcode() == Opcode.invokestatic)
					constraintValue = AbstractConstraintValue.NULL_VALUE;

				/** no premature value and accessible object is a method that can get invoked */
				if (!argumentValues.hasPrematureArgument && constraintValue instanceof AbstractConstraintLiteral<?>
						&& ((AbstractConstraintLiteral<?>) constraintValue).isFinishedType()
						&& (bytecodeLine.getOpcode() == Opcode.invokestatic || !(constraintValue instanceof AbstractConstraintClass))) {
					constraintLiteral = (AbstractConstraintLiteral<?>) constraintValue;

					/** get argument values from abstract constraint values in argument list */
					Object[] arguments = new Object[argumentValues.size()];
					for (int i=0; i<argumentValues.size(); i++)
						arguments[i] = ((AbstractConstraintLiteral<?>) argumentValues.get(i)).getValue();

					/** COMMENT */
					this.stack.push(
							this.invokeAccessibleObject(bytecodeLineConstantTableAccessibleObject, constraintLiteral, arguments));
				}
				/** accessible object is a method and class file can get loaded from the classloader */
				else if (bytecodeLineConstantTableAccessibleObject.getAccessibleObject() instanceof Method
						&& ((Method) bytecodeLineConstantTableAccessibleObject.getAccessibleObject()).getDeclaringClass().getClassLoader() != null) {

					DisassembledMethod disassembledSubMethod = KoselleckUtils.getDisassembledMethod((Method) bytecodeLineConstantTableAccessibleObject.getAccessibleObject());
					AbstractConstraint abstractConstraint = new Decompiler().decompile(
							disassembledSubMethod.getMethod(), disassembledSubMethod.getBytecodeLines(), constraintValue, argumentValues.toArray(new AbstractConstraintValue[0]));

					/** COMMENT */
					this.stack.push(
							this.getSubMethodConstraintValue(abstractConstraint, constraintValue, preFields));
				}
				/** class file can not get loaded from the classloader (e.g. java.lang classes) */
				else
					this.stack.push(new AbstractPrematureConstraintValueAccessibleObject(
							constraintValue, bytecodeLineConstantTableAccessibleObject.getAccessibleObject(), argumentValues));

				break;

			case tableswitch:
				bytecodeLineTableswitch = (BytecodeLineTableswitch) bytecodeLine;

				constraintValue = this.stack.pop();

				if (constraintValue instanceof AbstractConstraintLiteralInteger) {
					Integer caseOffset = bytecodeLineTableswitch.getOffsetsMap().get(((AbstractConstraintLiteralInteger) constraintValue).getValue().toString());
					if (caseOffset == null) {
						caseOffset = bytecodeLineTableswitch.getOffsetsMap().get("default");
						if (caseOffset == null) {
							String message = "neither a case for value \"" + ((Integer) constraintLiteral.getValue()).toString() + "\" nor a default case is defined.";
							Logger.getLogger(Decompiler.class).fatal(message);
							throw new UnknownSwitchCaseException(message);
						} else
							nextOffset = caseOffset;
					} else
						nextOffset = caseOffset;
				} else
					return this.getTableswitchConstraint(
							constraintValue, bytecodeLineTableswitch.getOffsetsMap(), bytecodeLineTableswitch.getOffsetsMap().keySet().iterator(), bytecodeLineTableswitch.getOffsetsMap().get("default"), bytecodeLines);

				break;

			case dup:
				this.stack.push(this.stack.peek());
				break;

			case _goto:
				bytecodeLineOffset = (BytecodeLineOffset) bytecodeLine;

				nextOffset = bytecodeLineOffset.getOffset();
				break;

			case ifeq:
			case iflt:
			case ifle:
			case ifgt:
			case ifge:
			case ifne:
				bytecodeLineOffset = (BytecodeLineOffset) bytecodeLine;
				constraintOperator = ConstraintOperator.fromOpcode(bytecodeLine.getOpcode().getName());

				constraintValue = this.stack.pop();

				if (constraintValue instanceof AbstractConstraintLiteral<?>
						&& ((AbstractConstraintLiteral<?>) constraintValue).isNumberType()) {
					constraintLiteral = (AbstractConstraintLiteral<?>) constraintValue;

					boolean equalsZero;
					if (constraintValue instanceof AbstractConstraintLiteralDouble)
						equalsZero = constraintOperator.compare(((AbstractConstraintLiteralDouble) constraintLiteral).getValue(), 0d);
					else if (constraintValue instanceof AbstractConstraintLiteralFloat)
						equalsZero = constraintOperator.compare(((AbstractConstraintLiteralFloat) constraintLiteral).getValue(), 0f);
					else if (constraintValue instanceof AbstractConstraintLiteralInteger)
						equalsZero = constraintOperator.compare(((AbstractConstraintLiteralInteger) constraintLiteral).getValue(), 0);
					else
						equalsZero = constraintOperator.compare((Integer) constraintLiteral.getValue(), 0);

					if (equalsZero)
						nextOffset = bytecodeLineOffset.getOffset();
					else
						nextOffset = bytecodeLineOffset.getFollowingLineNumber();
				} else
					return new AbstractIfThenElseConstraint(
							new AbstractSingleConstraint(
									constraintValue, constraintOperator, new AbstractConstraintLiteralInteger(0)),
							this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.getOffset()),
							this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.getFollowingLineNumber()));

				break;

			case if_Xcmpne:
			case if_Xcmpge:
			case if_Xcmpgt:
			case if_Xcmple:
			case if_Xcmplt:
			case if_Xcmpeq:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();

				bytecodeLineOffset = (BytecodeLineOffset) bytecodeLine;

				return new AbstractIfThenElseConstraint(
						this.getSingleConstraint(
								constraintValue1, ConstraintOperator.fromOpcode(bytecodeLineOffset.getOpcode().getName()), constraintValue2),
						this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.getOffset()),
						this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.getFollowingLineNumber()));

			case fcmpg:
			case fcmpl:
			case dcmpg:
			case dcmpl:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();

				if ((constraintValue1 instanceof AbstractConstraintLiteral<?>)
						&& (constraintValue1 instanceof AbstractConstraintLiteral<?>)) {
					constraintLiteral1 = (AbstractConstraintLiteral<?>)constraintValue1;
					constraintLiteral2 = (AbstractConstraintLiteral<?>)constraintValue2;

					if ((bytecodeLine.getOpcode() == Opcode.dcmpg || bytecodeLine.getOpcode() == Opcode.dcmpl)
							&& constraintLiteral1.getValue() instanceof Double && constraintLiteral2.getValue() instanceof Double)
						this.stack.push(new AbstractConstraintLiteralInteger(
								constraintLiteral1.compareTo(constraintLiteral2)));
					else if ((bytecodeLine.getOpcode() == Opcode.fcmpg || bytecodeLine.getOpcode() == Opcode.fcmpl)
							&& constraintLiteral1.getValue() instanceof Float && constraintLiteral2.getValue() instanceof Float)
						this.stack.push(new AbstractConstraintLiteralInteger(
								constraintLiteral1.compareTo(constraintLiteral2)));
					else
						this.stack.push(
								new AbstractConstraintFormula(
										constraintValue1, ArithmeticOperator.SUB, constraintValue2));
				} else
					this.stack.push(
							new AbstractConstraintFormula(
									constraintValue1, ArithmeticOperator.SUB, constraintValue2));

				break;

			case _return:
				returnValue = this.stack.pop();

				if (returnValue instanceof AbstractConstraintLiteral<?>) {
					AbstractConstraintLiteral<?> returnLiteral = (AbstractConstraintLiteral<?>) returnValue;
					if (returnLiteral.isNumberType())
						return new AbstractBooleanConstraint(!returnLiteral.getValue().equals(0), returnValue);
					else
						return new AbstractBooleanConstraint(true, returnValue);
				} else
					return new AbstractBooleanConstraint(true, returnValue);

			default:
				UnknownOpcodeException exception = new UnknownOpcodeException(bytecodeLine.getOpcode());
				Logger.getLogger(Decompiler.class).fatal(exception.getMessage());
				throw exception;
			}

			bytecodeLine = bytecodeLines.get(nextOffset);
		} while (nextOffset > 0);

		/** should never happen; should always return constraint in while-loop */
		String message = "bytecode of (constraint) method should always return (boolean) value";
		Logger.getLogger(Decompiler.class).fatal(message);
		throw new DecompilerException(message);
	}

	/**
	 * getCalculatedValue returns an abstract constraint value for the given
	 *  constraint values and the arithmetic operator. If the constraint values
	 *  are both numbers the new value is calculated, otherwise a new abstract
	 *  constraint formula is returned.
	 * 
	 * @param constraintValue1 the first abstract constraint value
	 * @param operator the arithmetic operator to calculate the values
	 * @param constraintValue2 the second abstract constraint value
	 * 
	 * @return the calculated value as an abstract constraint literal if both
	 *  values are numbers, a new abstract constraint formula with the abstract
	 *  constraint values and the arithmetic operator otherwise
	 */
	private AbstractConstraintValue getCalculatedValue(AbstractConstraintValue constraintValue1, ArithmeticOperator operator, AbstractConstraintValue constraintValue2) {
		if (constraintValue1 instanceof AbstractConstraintLiteral<?>
				&& constraintValue2 instanceof AbstractConstraintLiteral<?>) {
			AbstractConstraintLiteral<?> constraintLiteral1 = (AbstractConstraintLiteral<?>) constraintValue1;
			AbstractConstraintLiteral<?> constraintLiteral2 = (AbstractConstraintLiteral<?>) constraintValue2;

			if (constraintLiteral1.isNumberType() && constraintLiteral2.isNumberType())
				return constraintLiteral1.calc(constraintLiteral2, operator);
			else
				return new AbstractConstraintFormula(
						constraintLiteral1, operator, constraintLiteral2);
		} else
			return new AbstractConstraintFormula(
					constraintValue1, operator, constraintValue2);
	}

	/**
	 * getSingleConstraint returns an abstract constraint for the given
	 *  abstract constraint values and the constraint operator. If the
	 *  constraint values are both numbers the boolean value is calculated,
	 *  otherwise a new abstract single constraint is returned.
	 * 
	 * @param constraintValue1 the first abstract constraint value
	 * @param constraintOperator the constraint operator
	 * @param constraintValue2 the second abstract constraint value
	 * 
	 * @return the calculated boolean value as an abstract constraint if both
	 *  values are numbers, a new abstract single constraint with the abstract
	 *  constraint values and the constraint operator otherwise
	 */
	private AbstractConstraint getSingleConstraint(AbstractConstraintValue constraintValue1, ConstraintOperator operator, AbstractConstraintValue constraintValue2) {
		if (constraintValue1 instanceof AbstractConstraintLiteral<?>
				&& constraintValue2 instanceof AbstractConstraintLiteral<?>) {
			AbstractConstraintLiteral<?> constraintLiteral1 = (AbstractConstraintLiteral<?>) constraintValue1;
			AbstractConstraintLiteral<?> constraintLiteral2 = (AbstractConstraintLiteral<?>) constraintValue2;

			if (constraintLiteral1.isFinishedNumberType() && constraintLiteral2.isFinishedNumberType())
				return ConstraintUtils.evaluateNumberTypes(
						constraintLiteral1, operator, constraintLiteral2);
			else
				return new AbstractSingleConstraint(
						constraintLiteral1, operator, constraintLiteral2);
		} else
			return new AbstractSingleConstraint(
					constraintValue1, operator, constraintValue2);
	}

	/**
	 * COMMENT
	 * 
	 * @param constraintValue
	 * @param offsetsMap
	 * @param offsetsMapKeyIterator
	 * @param defaultOffset
	 * @param bytecodeLines
	 * @param prefixedFields
	 * 
	 * @return
	 */
	private AbstractConstraint getTableswitchConstraint(AbstractConstraintValue constraintValue, Map<String, Integer> offsetsMap, Iterator<String> offsetsMapKeyIterator, Integer defaultOffset, Map<Integer, BytecodeLine> bytecodeLines) {
		if (offsetsMapKeyIterator.hasNext()) {
			String offsetsKey = offsetsMapKeyIterator.next();
			if (offsetsKey.matches("\\d+"))
				return new AbstractIfThenElseConstraint(
						new AbstractSingleConstraint(constraintValue, ConstraintOperator.EQUAL,
								new AbstractConstraintLiteralInteger(Integer.parseInt(offsetsKey))),
						this.parseMethodBytecode(bytecodeLines, offsetsMap.get(offsetsKey)),
						this.getTableswitchConstraint(constraintValue, offsetsMap, offsetsMapKeyIterator, defaultOffset, bytecodeLines));
			else if (offsetsKey.equals("default"))
				return this.getTableswitchConstraint(constraintValue, offsetsMap, offsetsMapKeyIterator, defaultOffset, bytecodeLines);
			else {
				String message = "case of a tableswitch needs to be integer or default case but is \"" + offsetsKey + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new MissformattedBytecodeLineException(message);
			}
		} else {
			if (defaultOffset != null)
				return this.parseMethodBytecode(bytecodeLines, defaultOffset);
			else
				return new AbstractBooleanConstraint(false);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLineConstantTableAccessibleObject
	 * @param constraintValue
	 * 
	 * @return
	 */
	private AbstractConstraintValue getFieldValue(BytecodeLineConstantTableAccessibleObject bytecodeLineConstantTableAccessibleObject, AbstractConstraintValue constraintValue) {
		Field bytecodeLineField = (Field) bytecodeLineConstantTableAccessibleObject.getAccessibleObject();

		if (constraintValue instanceof AbstractConstraintLiteral<?> && ((AbstractConstraintLiteral<?>) constraintValue).isFinishedType() && bytecodeLineField.getAnnotation(Variable.class) == null) {
			boolean accessibility = bytecodeLineField.isAccessible();
			bytecodeLineField.setAccessible(true);

			Object value;
			try {
				value = bytecodeLineField.get(((AbstractConstraintLiteral<?>) constraintValue).getValue());
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not get field \"" + bytecodeLineField.getName() + "\" for value \"" + constraintValue + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new IllegalArgumentException(message);
			} finally {
				bytecodeLineField.setAccessible(accessibility);
			}

			if (ClassUtils.isDoubleClass(bytecodeLineField.getType()))
				return new AbstractConstraintLiteralDouble((Double) value);
			else if (ClassUtils.isFloatClass(bytecodeLineField.getType()))
				return new AbstractConstraintLiteralFloat((Float) value);
			else if (ClassUtils.isIntegerClass(bytecodeLineField.getType()))
				return new AbstractConstraintLiteralInteger((Integer) value);
			else if (bytecodeLineField.getType().isEnum())
				return new AbstractConstraintLiteralInteger(((Enum<?>) value).ordinal());
			else
				return new AbstractConstraintLiteralObject(value);
		} else if (constraintValue instanceof AbstractConstraintLiteral<?> || constraintValue instanceof AbstractConstraintClass) {
			List<PreField> preFields = new ArrayList<PreField>();
			if (!(constraintValue instanceof AbstractConstraintClass)) {
				preFields.addAll(constraintValue.getPreFieldList());
				preFields.add(((AbstractConstraintLiteral<?>) constraintValue).toPreField());
			}

			if (ClassUtils.isIntegerClass(bytecodeLineField.getType()))
				return new AbstractConstraintLiteralInteger(bytecodeLineField,
						constraintValue.getFieldCodeIndex(),
						constraintValue.getOpcode(),
						bytecodeLineConstantTableAccessibleObject.getConstantTableIndex(),
						preFields);
			else if (ClassUtils.isFloatClass(bytecodeLineField.getType()))
				return new AbstractConstraintLiteralFloat(bytecodeLineField,
						constraintValue.getFieldCodeIndex(),
						constraintValue.getOpcode(),
						bytecodeLineConstantTableAccessibleObject.getConstantTableIndex(),
						preFields);
			else if (ClassUtils.isDoubleClass(bytecodeLineField.getType()))
				return new AbstractConstraintLiteralDouble(bytecodeLineField,
						constraintValue.getFieldCodeIndex(),
						constraintValue.getOpcode(),
						bytecodeLineConstantTableAccessibleObject.getConstantTableIndex(),
						preFields);
			else if (bytecodeLineField.getType().isEnum())
				return new AbstractConstraintLiteralEnum(bytecodeLineField,
						constraintValue.getFieldCodeIndex(),
						constraintValue.getOpcode(),
						bytecodeLineConstantTableAccessibleObject.getConstantTableIndex(),
						preFields);
			else
				return new AbstractConstraintLiteralObject(bytecodeLineField,
						constraintValue.getFieldCodeIndex(),
						constraintValue.getOpcode(),
						bytecodeLineConstantTableAccessibleObject.getConstantTableIndex(),
						preFields);
		} else {
			String message = "abstract constraint value \"" + constraintValue + "\" needs to be of class or literal type but has type \"" + constraintValue.getClass().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLineConstantTableAccessibleObject
	 * @param constraintValue
	 * 
	 * @return
	 */
	private AbstractConstraintValue getStaticFieldValue(BytecodeLineConstantTableAccessibleObject bytecodeLineConstantTableAccessibleObject, AbstractConstraintValue constraintValue) {
		Field bytecodeLineField = (Field) bytecodeLineConstantTableAccessibleObject.getAccessibleObject();

		/** non-variable static field */
		if (bytecodeLineField.getAnnotation(Variable.class) == null) {
			bytecodeLineField.setAccessible(true);
			try {
				if (ClassUtils.isDoubleClass(bytecodeLineField.getType()))
					return new AbstractConstraintLiteralDouble(
							(Double) bytecodeLineField.get(null));
				else if (ClassUtils.isFloatClass(bytecodeLineField.getType()))
					return new AbstractConstraintLiteralFloat(
							(Float) bytecodeLineField.get(null));
				else if (ClassUtils.isIntegerClass(bytecodeLineField.getType()))
					return new AbstractConstraintLiteralInteger(
							(Integer) bytecodeLineField.get(null));
				else
					return new AbstractConstraintLiteralObject(
							bytecodeLineField.get(null));
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not access static field \"" + bytecodeLineField.getName() +"\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		}
		/** variable static field */
		else
			return this.getFieldValue(bytecodeLineConstantTableAccessibleObject, constraintValue);
	}

	/**
	 * COMMENT
	 * 
	 * @param accessibleObject
	 * 
	 * @return
	 */
	private ArgumentList getArgumentList(AccessibleObject accessibleObject) {
		/** get count of parameters */
		int parameterCount;
		if (accessibleObject instanceof Method)
			parameterCount = ((Method) accessibleObject).getParameterTypes().length;
		else if (accessibleObject instanceof Constructor<?>)
			parameterCount = ((Constructor<?>) accessibleObject).getParameterTypes().length;
		else {
			String message = "accessible object needs to be method or constructor but is \"" + accessibleObject.getClass().getName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		/** pop argument values from stack */
		ArgumentList argumentValues = new ArgumentList();
		for (int i=0; i<parameterCount; i++) {
			AbstractConstraintValue argument = this.stack.pop();
			if (!argumentValues.hasPrematureArgument()
					&& (!(argument instanceof AbstractConstraintLiteral<?>)
							|| !((AbstractConstraintLiteral<?>) argument).isFinishedType()))
				argumentValues.setHasPrematureArgument(true);
			argumentValues.add(argument);
		}
		Collections.reverse(argumentValues);

		return argumentValues;
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine
	 * @param constraintValue
	 * @param arguments
	 * 
	 * @return
	 */
	private AbstractConstraintLiteral<?> invokeAccessibleObject(BytecodeLineConstantTableAccessibleObject bytecodeLine, AbstractConstraintValue constraintValue, Object[] arguments) {
		AccessibleObject accessibleObject = bytecodeLine.getAccessibleObject();

		/** COMMENT */
		if (accessibleObject instanceof Method) {
			Object invokationObject;
			if (bytecodeLine.getOpcode() != Opcode.invokestatic
					&& constraintValue instanceof AbstractConstraintLiteral<?>
					&& ClassUtils.classesEquals(
							((AbstractConstraintLiteral<?>) constraintValue).getValue().getClass(),
							((Method) accessibleObject).getDeclaringClass()))
				invokationObject = ((AbstractConstraintLiteral<?>) constraintValue).getValue();
			else if (bytecodeLine.getOpcode() == Opcode.invokestatic
					&& constraintValue instanceof AbstractConstraintClass)
				invokationObject = null;
			else {
				String message = "could not get invokation object for accessible object \"" + accessibleObject + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
				
			Method lineMethod = (Method) accessibleObject;

			/** try to invoke method */
			try {
				/** push result of invoked method to stack */
				if (ClassUtils.isDoubleClass(lineMethod.getReturnType()))
					return new AbstractConstraintLiteralDouble(
							(Double) lineMethod.invoke(invokationObject, arguments));
				else if (ClassUtils.isFloatClass(lineMethod.getReturnType()))
					return new AbstractConstraintLiteralFloat(
							(Float) lineMethod.invoke(invokationObject, arguments));
				else if (ClassUtils.isIntegerClass(lineMethod.getReturnType()))
					return new AbstractConstraintLiteralInteger(
							(Integer) lineMethod.invoke(invokationObject, arguments));
				else
					return new AbstractConstraintLiteralObject(
							lineMethod.invoke(invokationObject, arguments));
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
				String message = "could not invoke method \"" + lineMethod.toGenericString().replaceAll(".*\\s(\\S+)$", "$1") + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		}
		/** COMMENT */
		else if (accessibleObject instanceof Constructor<?>
				&& bytecodeLine.getOpcode() != Opcode.invokestatic
				&& constraintValue instanceof AbstractConstraintClass
				&& ClassUtils.classesEquals(
						((AbstractConstraintClass) constraintValue).getValue(),
						((Constructor<?>) accessibleObject).getDeclaringClass())) {
			Constructor<?> lineConstructor = (Constructor<?>) accessibleObject;
			/** try to instantiate class */
			try {
				/** push new instantiation of class to stack */
				if (ClassUtils.isDoubleClass(lineConstructor.getDeclaringClass()))
					return new AbstractConstraintLiteralDouble(
							(Double) lineConstructor.newInstance(arguments));
				else if (ClassUtils.isFloatClass(lineConstructor.getDeclaringClass()))
					return new AbstractConstraintLiteralFloat(
							(Float) lineConstructor.newInstance(arguments));
				else if (ClassUtils.isIntegerClass(lineConstructor.getDeclaringClass()))
					return new AbstractConstraintLiteralInteger(
							(Integer) lineConstructor.newInstance(arguments));
				else
					return new AbstractConstraintLiteralObject(
							lineConstructor.newInstance(arguments));
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | InstantiationException e) {
				String message = "could not instantiate new \"" + lineConstructor.getDeclaringClass().getName() + "\" \"" + lineConstructor.getName() + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		}
		/** COMMENT */
		else {
			String message = "no valid access to accessible object \"" + accessibleObject + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param abstractConstraint
	 * @param outerConstraintValue
	 * @param preFields
	 * 
	 * @return
	 */
	private AbstractConstraintValue getSubMethodConstraintValue(AbstractConstraint abstractConstraint, AbstractConstraintValue outerConstraintValue, List<PreField> preFields) {
		if (abstractConstraint instanceof AbstractBooleanConstraint
				&& ((AbstractBooleanConstraint) abstractConstraint).getValue()) {
			AbstractConstraintValue innerConstraintValue = ((AbstractBooleanConstraint) abstractConstraint).getReturnValue();

			if (innerConstraintValue instanceof AbstractConstraintLiteral<?>) {
				AbstractConstraintLiteral<?> innerConstraintLiteral = (AbstractConstraintLiteral<?>) innerConstraintValue; 

				if (innerConstraintLiteral.isFinishedType())
					return innerConstraintLiteral;
				else if (innerConstraintLiteral.isUnfinishedFieldType()) {
					if (outerConstraintValue instanceof AbstractConstraintClass || outerConstraintValue instanceof AbstractConstraintLiteralObject) {
						AbstractConstraintLiteral<?> mergedConstraintLiteral = this.getMergedConstraintLiteral(
								outerConstraintValue, innerConstraintLiteral);

						preFields.add(mergedConstraintLiteral.toPreField());

						return mergedConstraintLiteral;
					} else if(outerConstraintValue instanceof AbstractConstraintLiteral<?>)
						return outerConstraintValue;
					else {
						String message = "outer constraint value \"" + outerConstraintValue + "\" is of unsupported type \"" + outerConstraintValue.getClass().getSimpleName() + "\"";
						Logger.getLogger(Decompiler.class).fatal(message);
						throw new DecompilerException(message);
					}
				} else {
					String message = "inner constraint literal \"" + innerConstraintLiteral + "\" is neither finished nor of field type";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new DecompilerException(message);
				}
			} else {
				String message = "inner constraint value \"" + innerConstraintValue + "\" needs to be a literal type but is of type \"" + innerConstraintValue.getClass().getSimpleName() + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
		} else 
			return new AbstractPrematureConstraintValueConstraint(abstractConstraint);
	}

	/**
	 * COMMENT
	 * 
	 * @param outerValue
	 * @param innerLiteral
	 * 
	 * @return
	 */
	private AbstractConstraintLiteral<?> getMergedConstraintLiteral(AbstractConstraintValue outerValue, AbstractConstraintLiteral<?> innerLiteral) {
		List<PreField> newPreFields = new ArrayList<PreField>();
		newPreFields.addAll(outerValue.getPreFieldList());
		newPreFields.addAll(innerLiteral.getPreFieldList());

		if (innerLiteral instanceof AbstractConstraintLiteralInteger)
			return new AbstractConstraintLiteralInteger(
					innerLiteral.getField(), outerValue.getFieldCodeIndex(), outerValue.getOpcode(), innerLiteral.getConstantTableIndex(), newPreFields);
		else if (innerLiteral instanceof AbstractConstraintLiteralFloat)
			return new AbstractConstraintLiteralFloat(
					innerLiteral.getField(), outerValue.getFieldCodeIndex(), outerValue.getOpcode(), innerLiteral.getConstantTableIndex(), newPreFields);
		else if (innerLiteral instanceof AbstractConstraintLiteralDouble)
			return new AbstractConstraintLiteralDouble(
					innerLiteral.getField(), outerValue.getFieldCodeIndex(), outerValue.getOpcode(), innerLiteral.getConstantTableIndex(), newPreFields);
		else if (innerLiteral instanceof AbstractConstraintLiteralObject)
			return new AbstractConstraintLiteralObject(
					innerLiteral.getField(), outerValue.getFieldCodeIndex(), outerValue.getOpcode(), innerLiteral.getConstantTableIndex(), newPreFields);
		else {
			RuntimeException exception = new UnsupportedConstraintLiteralException(innerLiteral);
			Logger.getLogger(Decompiler.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private class ArgumentList extends ArrayList<AbstractConstraintValue> {
		/** COMMENT */
		private static final long serialVersionUID = 4116003574027287498L;

		/** COMMENT */
		private boolean hasPrematureArgument;

		/**
		 * COMMENT
		 */
		public ArgumentList() {
			this.hasPrematureArgument = false;
		}

		/**
		 * COMMENT
		 * 
		 * @return
		 */
		public boolean hasPrematureArgument() {
			return this.hasPrematureArgument;
		}

		/**
		 * COMMENT
		 * 
		 * @param hasPrematureArgument
		 */
		public void setHasPrematureArgument(boolean hasPrematureArgument) {
			this.hasPrematureArgument = hasPrematureArgument;
		}
	}
}
