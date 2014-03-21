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
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralClass;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralDouble;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralField;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralFloat;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintValue;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractPrematureConstraintValue;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineConstantTableAccessibleObject;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineConstantTableClass;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineOffset;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineTableswitch;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineValue;
import de.agra.sat.koselleck.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;
import de.agra.sat.koselleck.exceptions.UnknownOpcodeException;
import de.agra.sat.koselleck.exceptions.UnknownSwitchCaseException;
import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.types.Opcode;
import de.agra.sat.koselleck.utils.CompareUtils;
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
				disassembledMethod.method, disassembledMethod.bytecodeLines, invokationValue, argumentValues);
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
		AbstractConstraintValue innerConstraintValue = null;
		AbstractConstraintLiteral<?> constraintLiteral = null;
		AbstractConstraintLiteral<?> innerConstraintLiteral = null;
		AbstractConstraintValue constraintValue1 = null;
		AbstractConstraintValue constraintValue2 = null;
		AbstractConstraintLiteral<?> constraintLiteral1 = null;
		AbstractConstraintLiteral<?> constraintLiteral2 = null;

		AbstractConstraintLiteralField constraintLiteralField = null;
		AbstractConstraintLiteralField innerConstraintLiteralField = null;

		AbstractConstraintLiteralClass constraintLiteralClass = null;

		AbstractConstraintValue returnValue = null;

		ConstraintOperator constraintOperator = null;

		Method lineMethod = null;
		Constructor<?> lineConstructor = null;
		ArgumentList argumentValues = null;
		
		do {
			nextOffset = bytecodeLine.followingLineNumber;
			
			switch(bytecodeLine.opcode) {
			case load_:
			case load:
				this.stack.push(this.store.get(((BytecodeLineValue)bytecodeLine).value));
				break;
				
			case store_:
			case store:
				this.store.put((Integer)((BytecodeLineValue)bytecodeLine).value, this.stack.pop());
				break;
				
			case _const:
			case _const_:
			case bipush:
				this.stack.push(
						new AbstractConstraintLiteralInteger((Integer)((BytecodeLineValue)bytecodeLine).value));
				break;
				
			case getfield:
				bytecodeLineConstantTableAccessibleObject = (BytecodeLineConstantTableAccessibleObject) bytecodeLine;
				
				constraintValue = this.stack.pop();
				if (!(constraintValue instanceof AbstractConstraintLiteral<?>)) {
					String message = "could not get field \"" + bytecodeLineConstantTableAccessibleObject.accessibleObject + "\" because constraint value is no literal type";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}
				
				this.stack.push(
						this.getField(bytecodeLineConstantTableAccessibleObject, (AbstractConstraintLiteral<?>) constraintValue, preFields));
				
				break;
			case getstatic:
				bytecodeLineConstantTableAccessibleObject = (BytecodeLineConstantTableAccessibleObject) bytecodeLine;
				
				constraintValue = this.stack.pop();
				if (!(constraintValue instanceof AbstractConstraintLiteralField)) {
					String message = "could not get field";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}
				
				this.stack.push(
						this.getStaticField(bytecodeLineConstantTableAccessibleObject, (AbstractConstraintLiteralField) constraintValue, preFields));
				
				break;
				
			case checkcast:
				constraintValue = this.stack.pop();
				if (!(constraintValue instanceof AbstractConstraintLiteralField)) {
					String message = "could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new ClassCastException(message);
				}
				
				Field cField = ((AbstractConstraintLiteralField)constraintValue).value;
				if (!cField.getType().isAssignableFrom(((BytecodeLineConstantTableClass)bytecodeLine).clazz)) {
					String message = "could not cast from \"" + cField.getType().getSimpleName() + "\" to \"" + ((BytecodeLineConstantTableClass)bytecodeLine).clazz.getSimpleName() + "\"";
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
								new AbstractConstraintLiteralDouble(new Double((Integer) constraintLiteral.value)));
					} else if (constraintLiteral.isNumberType) {
						String message = "could not cast constraint value \"" + constraintLiteral.value + "\" (" + constraintLiteral.value.getClass().getSimpleName() + ") to integer";
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
						/** push corresponding double to stack */
						this.stack.push(
								new AbstractConstraintLiteralFloat(new Float((Integer) constraintLiteral.value)));
					} else if (constraintLiteral.isNumberType) {
						String message = "could not cast constraint value \"" + constraintLiteral.value + "\" (" + constraintLiteral.value.getClass().getSimpleName() + ") to integer";
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
					
					/** check for integer */
					if (constraintLiteral instanceof AbstractConstraintLiteralFloat) {
						/** push corresponding double to stack */
						this.stack.push(
								new AbstractConstraintLiteralDouble(new Double((Float) constraintLiteral.value)));
					} else if (constraintLiteral.isNumberType) {
						String message = "could not cast constraint value \"" + constraintLiteral.value + "\" (" + constraintLiteral.value.getClass().getSimpleName() + ") to integer";
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

				if (CompareUtils.equalsAny(bytecodeLineValue.value.getClass(), CompareUtils.doubleClasses))
					this.stack.push(new AbstractConstraintLiteralDouble((Double) bytecodeLineValue.value));
				else if (CompareUtils.equalsAny(bytecodeLineValue.value.getClass(), CompareUtils.floatClasses))
					this.stack.push(new AbstractConstraintLiteralFloat((Float) bytecodeLineValue.value));
				else if (CompareUtils.equalsAny(bytecodeLineValue.value.getClass(), CompareUtils.integerClasses))
					this.stack.push(new AbstractConstraintLiteralInteger((Integer) bytecodeLineValue.value));
				else
					this.stack.push(new AbstractConstraintLiteralObject(bytecodeLineValue.value));

				break;

			case add:
			case sub:
			case mul:
			case div:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				this.stack.push(this.getCalculatedValue(
						constraintValue1, ArithmeticOperator.fromOpcode(bytecodeLine.opcode), constraintValue2));
				break;
				
			case _new:
				bytecodeLineConstantTableClass = (BytecodeLineConstantTableClass)bytecodeLine;
				this.stack.push(
						new AbstractConstraintLiteralClass(bytecodeLineConstantTableClass.clazz, Opcode._new, -1));
				break;
				
			case invokestatic:
			case invokevirtual:
			case invokespecial:
				bytecodeLineConstantTableAccessibleObject = (BytecodeLineConstantTableAccessibleObject)bytecodeLine;

				/** get arguments for method or constructor */
				argumentValues = this.getArgumentList(bytecodeLineConstantTableAccessibleObject.accessibleObject);

				/** pop value from stack */
				constraintValue = this.stack.pop();

				/** no premature value and accessible object is a method that can get invoked */
				if (!argumentValues.hasPrematureArgument && constraintValue instanceof AbstractConstraintLiteral<?>
						&& !(constraintValue instanceof AbstractConstraintLiteralField)
						&& (bytecodeLine.opcode == Opcode.invokestatic || !(constraintValue instanceof AbstractConstraintLiteralClass))) {
					constraintLiteral = (AbstractConstraintLiteral<?>)constraintValue;

					/** get argument values from abstract constraint values in argument list */
					Object[] arguments = new Object[argumentValues.size()];
					for (int i=0; i<argumentValues.size(); i++)
						arguments[i] = ((AbstractConstraintLiteral<?>)argumentValues.get(i)).value;

					/**  */
					if (bytecodeLineConstantTableAccessibleObject.accessibleObject instanceof Method
							&& bytecodeLine.opcode != Opcode.invokestatic
							&& CompareUtils.classesEquals(
									constraintLiteral.value.getClass(),
									((Method)bytecodeLineConstantTableAccessibleObject.accessibleObject).getDeclaringClass())) {
						lineMethod = (Method)bytecodeLineConstantTableAccessibleObject.accessibleObject;
						/** try to invoke method */
						try {
							/** push result of invoked method to stack */
							if (CompareUtils.equalsAny(lineMethod.getReturnType(), CompareUtils.doubleClasses))
								this.stack.push(new AbstractConstraintLiteralDouble(
										(Double) lineMethod.invoke(constraintLiteral.value, arguments)));
							else if (CompareUtils.equalsAny(lineMethod.getReturnType(), CompareUtils.floatClasses))
								this.stack.push(new AbstractConstraintLiteralFloat(
										(Float) lineMethod.invoke(constraintLiteral.value, arguments)));
							else if (CompareUtils.equalsAny(lineMethod.getReturnType(), CompareUtils.integerClasses))
								this.stack.push(new AbstractConstraintLiteralInteger(
										(Integer) lineMethod.invoke(constraintLiteral.value, arguments)));
							else
								this.stack.push(new AbstractConstraintLiteralObject(
										lineMethod.invoke(constraintLiteral.value, arguments)));
						} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
							String message = "could not invoke method \"" + lineMethod.toGenericString().replaceAll(".*\\s(\\S+)$", "$1") + "\"";
							Logger.getLogger(Decompiler.class).fatal(message);
							throw new IllegalArgumentException(message);
						}
					}
					/**  */
					else if (bytecodeLineConstantTableAccessibleObject.accessibleObject instanceof Method
							&& bytecodeLine.opcode == Opcode.invokestatic
							&& constraintLiteral instanceof AbstractConstraintLiteralClass) {
						lineMethod = (Method)bytecodeLineConstantTableAccessibleObject.accessibleObject;
						/** try to invoke method */
						try {
							/** push result of invoked method to stack */
							if (CompareUtils.equalsAny(lineMethod.getReturnType(), CompareUtils.doubleClasses))
								this.stack.push(new AbstractConstraintLiteralDouble(
										(Double) lineMethod.invoke(null, arguments)));
							else if (CompareUtils.equalsAny(lineMethod.getReturnType(), CompareUtils.floatClasses))
								this.stack.push(new AbstractConstraintLiteralFloat(
										(Float) lineMethod.invoke(null, arguments)));
							else if (CompareUtils.equalsAny(lineMethod.getReturnType(), CompareUtils.integerClasses))
								this.stack.push(new AbstractConstraintLiteralInteger(
										(Integer) lineMethod.invoke(null, arguments)));
							else
								this.stack.push(new AbstractConstraintLiteralObject(
										lineMethod.invoke(null, arguments)));
						} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
							String message = "could not invoke static method \"" + lineMethod.toGenericString().replaceAll(".*\\s(\\S+)$", "$1") + "\"";
							Logger.getLogger(Decompiler.class).fatal(message);
							throw new IllegalArgumentException(message);
						}
					}
					/**  */
					else if (bytecodeLineConstantTableAccessibleObject.accessibleObject instanceof Constructor<?>
							&& bytecodeLine.opcode != Opcode.invokestatic
							&& constraintLiteral instanceof AbstractConstraintLiteralClass
							&& CompareUtils.classesEquals(
									((AbstractConstraintLiteralClass)constraintLiteral).value,
									((Constructor<?>)bytecodeLineConstantTableAccessibleObject.accessibleObject).getDeclaringClass())) {
						lineConstructor = (Constructor<?>)bytecodeLineConstantTableAccessibleObject.accessibleObject;
						/** try to instantiate class */
						try {
							/** push new instantiation of class to stack */
							if (CompareUtils.equalsAny(lineConstructor.getDeclaringClass(), CompareUtils.doubleClasses))
								this.stack.push(new AbstractConstraintLiteralDouble(
										(Double) lineConstructor.newInstance(arguments)));
							else if (CompareUtils.equalsAny(lineConstructor.getDeclaringClass(), CompareUtils.floatClasses))
								this.stack.push(new AbstractConstraintLiteralFloat(
										(Float) lineConstructor.newInstance(arguments)));
							else if (CompareUtils.equalsAny(lineConstructor.getDeclaringClass(), CompareUtils.integerClasses))
								this.stack.push(new AbstractConstraintLiteralInteger(
										(Integer) lineConstructor.newInstance(arguments)));
							else
								this.stack.push(new AbstractConstraintLiteralObject(
										lineConstructor.newInstance(arguments)));
						} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | InstantiationException e) {
							String message = "could not instantiate new \"" + lineConstructor.getDeclaringClass().getName() + "\" \"" + lineConstructor.getName() + "\"";
							Logger.getLogger(Decompiler.class).fatal(message);
							throw new IllegalArgumentException(message);
						}
					}
					/**  */
					else {
						String message = "no valid access to accessible object \"" + bytecodeLineConstantTableAccessibleObject.accessibleObject + "\"";
						Logger.getLogger(Decompiler.class).fatal(message);
						throw new IllegalArgumentException(message);
					}
				}
				/** accessible object is a method and class file can get loaded from the classloader */
				else if (bytecodeLineConstantTableAccessibleObject.accessibleObject instanceof Method
						&& ((Method) bytecodeLineConstantTableAccessibleObject.accessibleObject).getDeclaringClass().getClassLoader() != null) {
					if (bytecodeLine.opcode == Opcode.invokestatic)
						constraintValue = AbstractConstraintValue.NULLValue;

					DisassembledMethod disassembledSubMethod = KoselleckUtils.getDisassembledMethod((Method) bytecodeLineConstantTableAccessibleObject.accessibleObject);
					AbstractConstraint abstractConstraint = new Decompiler().decompile(
							disassembledSubMethod.method, disassembledSubMethod.bytecodeLines, constraintValue, argumentValues.toArray(new AbstractConstraintValue[0]));
					
					if (abstractConstraint instanceof AbstractBooleanConstraint
							&& ((AbstractBooleanConstraint) abstractConstraint).value) {
						innerConstraintValue = ((AbstractBooleanConstraint) abstractConstraint).returnValue;

						if (constraintValue instanceof AbstractConstraintLiteral<?>
								&& innerConstraintValue instanceof AbstractConstraintLiteral<?>) {
							constraintLiteral = (AbstractConstraintLiteral<?>) constraintValue;
							innerConstraintLiteral = (AbstractConstraintLiteral<?>) innerConstraintValue; 
							
							if (innerConstraintLiteral instanceof AbstractConstraintLiteralField) {
								innerConstraintLiteralField = (AbstractConstraintLiteralField) innerConstraintLiteral;
								
								if (constraintLiteral instanceof AbstractConstraintLiteralField) {
									constraintLiteralField = (AbstractConstraintLiteralField) constraintLiteral;

									List<PreField> newPreFields = new ArrayList<PreField>();
									newPreFields.addAll(constraintLiteralField.preFields);
									newPreFields.addAll(innerConstraintLiteralField.preFields);

									preFields.add(new PreField(innerConstraintLiteralField.value,
											constraintLiteralField.constantTablePrefix + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
											constraintLiteralField.fieldCode, constraintLiteralField.fieldCodeIndex, new ArrayList<PreField>(newPreFields)));

									this.stack.push(new AbstractConstraintLiteralField(innerConstraintLiteralField.value,
											constraintLiteralField.constantTablePrefix + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
											constraintLiteralField.fieldCode, constraintLiteralField.fieldCodeIndex, newPreFields));
								} else if (constraintLiteral instanceof AbstractConstraintLiteralClass) {
									constraintLiteralClass = (AbstractConstraintLiteralClass) constraintLiteral;

									preFields.add(new PreField(innerConstraintLiteralField.value,
											"v_" + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
											constraintLiteralClass.fieldCode, constraintLiteralClass.fieldCodeIndex,
											new ArrayList<PreField>(innerConstraintLiteralField.preFields)));

									this.stack.push(new AbstractConstraintLiteralField(innerConstraintLiteralField.value,
											"v_" + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
											constraintLiteralClass.fieldCode, constraintLiteralClass.fieldCodeIndex,
											new ArrayList<PreField>(innerConstraintLiteralField.preFields)));
								} else
									throw new RuntimeException("TODO outer literal is no prefixed field"); // TODO implement								
							} else
								throw new RuntimeException("TODO invokevirtual --> inner literal is no prefixed field"); // TODO implement
						} else
							throw new RuntimeException("TODO invokevirtual --> no abstract constraint literal"); // TODO implement
					} else
						throw new RuntimeException("TODO invokevirtual --> no abstract boolean constraint"); // TODO implement
				}
				/** class file can not get loaded from the classloader (e.g. java.lang classes) */
				else
					this.stack.push(new AbstractPrematureConstraintValue(
							constraintValue, bytecodeLineConstantTableAccessibleObject.accessibleObject, argumentValues));
				
				break;
				
			case tableswitch:
				bytecodeLineTableswitch = (BytecodeLineTableswitch)bytecodeLine;
				
				constraintValue = this.stack.pop();
				
				if (constraintValue instanceof AbstractConstraintLiteralInteger) {
					Integer caseOffset = bytecodeLineTableswitch.offsetsMap.get(((AbstractConstraintLiteralInteger)constraintValue).value.toString());
					if (caseOffset == null) {
						caseOffset = bytecodeLineTableswitch.offsetsMap.get("default");
						if (caseOffset == null) {
							String message = "neither a case for value \"" + ((Integer)constraintLiteral.value).toString() + "\" nor a default case";
							Logger.getLogger(Decompiler.class).fatal(message);
							throw new UnknownSwitchCaseException(message);
						} else
							nextOffset = caseOffset;
					} else
						nextOffset = caseOffset;
				} else
					return this.getTableswitchConstraint(
							constraintValue, bytecodeLineTableswitch.offsetsMap, bytecodeLineTableswitch.offsetsMap.keySet().iterator(), bytecodeLineTableswitch.offsetsMap.get("default"), bytecodeLines, preFields);
				
				break;
				
			case dup:
				this.stack.push(this.stack.peek());
				break;
				
			case _goto:
				bytecodeLineOffset = (BytecodeLineOffset)bytecodeLine;
				
				nextOffset = bytecodeLineOffset.offset;
				break;
			
			case ifeq:
			case ifne:
				bytecodeLineOffset = (BytecodeLineOffset) bytecodeLine;
				
				if (bytecodeLineOffset.opcode == Opcode.ifeq)
					constraintOperator = ConstraintOperator.EQUAL;
				else if (bytecodeLineOffset.opcode == Opcode.ifne)
					constraintOperator = ConstraintOperator.NOT_EQUAL;
				
				constraintValue = this.stack.pop();
				
				if (constraintValue instanceof AbstractConstraintLiteral<?>
						&& ((AbstractConstraintLiteral<?>) constraintLiteral).isNumberType) {
					constraintLiteral = (AbstractConstraintLiteral<?>) constraintValue;
					
					if (constraintOperator.compare((Integer) constraintLiteral.value, 0))
						nextOffset = bytecodeLineOffset.offset;
					else
						nextOffset = bytecodeLineOffset.followingLineNumber;
				} else if (constraintValue instanceof AbstractConstraintLiteral<?>
						|| constraintValue instanceof AbstractConstraintFormula) {
					return new AbstractIfThenElseConstraint(
							new AbstractSingleConstraint(
									constraintValue, constraintOperator, new AbstractConstraintLiteralInteger(0), preFields),
							this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.offset),
							this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.followingLineNumber));
				} else {
					String message = "could not cast given value \"" + constraintLiteral + "\" to AbstractConstraintLiteral.";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new ClassCastException(message);
				}
				
				break;
				
			case if_icmpne:
			case if_icmpge:
			case if_icmpgt:
			case if_icmple:
			case if_icmplt:
			case if_icmpeq:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();

				bytecodeLineOffset = (BytecodeLineOffset)bytecodeLine;

				return new AbstractIfThenElseConstraint(
						this.getSingleConstraint(
								constraintValue1, ConstraintOperator.fromOpcode(bytecodeLineOffset.opcode.name), constraintValue2, preFields),
						this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.offset),
						this.parseMethodBytecode(bytecodeLines, bytecodeLineOffset.followingLineNumber));
			
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
					
					if ((bytecodeLine.opcode == Opcode.dcmpg || bytecodeLine.opcode == Opcode.dcmpl)
							&& constraintLiteral1.value instanceof Double && constraintLiteral2.value instanceof Double)
						this.stack.push(new AbstractConstraintLiteralInteger(
								constraintLiteral1.compareTo(constraintLiteral2)));
					else if ((bytecodeLine.opcode == Opcode.fcmpg || bytecodeLine.opcode == Opcode.fcmpl)
							&& constraintLiteral1.value instanceof Float && constraintLiteral2.value instanceof Float)
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
					if (returnLiteral.isNumberType)
						return new AbstractBooleanConstraint(!returnLiteral.value.equals(0), returnValue);
					else
						return new AbstractBooleanConstraint(true, returnValue);
				} else
					return new AbstractBooleanConstraint(true, returnValue);
				
			default:
				UnknownOpcodeException exception = new UnknownOpcodeException(bytecodeLine.opcode);
				Logger.getLogger(Decompiler.class).fatal(exception.getMessage());
				throw exception;
			}
			
			bytecodeLine = bytecodeLines.get(nextOffset);
		} while(nextOffset > 0);
		
		/** should never happen */
		return new AbstractBooleanConstraint(true, null);
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

			if (constraintLiteral1.isNumberType && constraintLiteral2.isNumberType)
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
	 * @param preFields the list of prefixed fields of the abstract constraint
	 *  values
	 * 
	 * @return the calculated boolean value as an abstract constraint if both
	 *  values are numbers, a new abstract single constraint with the abstract
	 *  constraint values and the constraint operator otherwise
	 */
	private AbstractConstraint getSingleConstraint(AbstractConstraintValue constraintValue1, ConstraintOperator operator, AbstractConstraintValue constraintValue2, List<PreField> preFields) {
		if (constraintValue1 instanceof AbstractConstraintLiteral<?>
				&& constraintValue2 instanceof AbstractConstraintLiteral<?>) {
			AbstractConstraintLiteral<?> constraintLiteral1 = (AbstractConstraintLiteral<?>)constraintValue1;
			AbstractConstraintLiteral<?> constraintLiteral2 = (AbstractConstraintLiteral<?>)constraintValue2;
			
			if (constraintLiteral1.isNumberType && constraintLiteral2.isNumberType)
				return ConstraintUtils.evaluateNumberTypes(
						constraintLiteral1, operator, constraintLiteral2);
			else
				return new AbstractSingleConstraint(
						constraintLiteral1, operator, constraintLiteral2, preFields);
		} else
			return new AbstractSingleConstraint(
					constraintValue1, operator, constraintValue2, preFields);
	}
	
	/**
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
	private AbstractConstraint getTableswitchConstraint(AbstractConstraintValue constraintValue, Map<String, Integer> offsetsMap, Iterator<String> offsetsMapKeyIterator, Integer defaultOffset, Map<Integer, BytecodeLine> bytecodeLines, List<PreField> preFields) {
		if (offsetsMapKeyIterator.hasNext()) {
			String offsetsKey = offsetsMapKeyIterator.next();
			if (offsetsKey.matches("\\d+"))
				return new AbstractIfThenElseConstraint(
						new AbstractSingleConstraint(constraintValue, ConstraintOperator.EQUAL, 
								new AbstractConstraintLiteralInteger(Integer.parseInt(offsetsKey)), preFields),
						this.parseMethodBytecode(bytecodeLines, offsetsMap.get(offsetsKey)),
						this.getTableswitchConstraint(constraintValue, offsetsMap, offsetsMapKeyIterator, defaultOffset, bytecodeLines, preFields));
			else if (offsetsKey.equals("default"))
				return this.getTableswitchConstraint(constraintValue, offsetsMap, offsetsMapKeyIterator, defaultOffset, bytecodeLines, preFields);
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
	 * 
	 * @param bytecodeLineConstantTableAccessibleObject
	 * @param constraintLiteral
	 * @param preFields
	 * 
	 * @return
	 */
	private AbstractConstraintValue getField(BytecodeLineConstantTableAccessibleObject bytecodeLineConstantTableAccessibleObject, AbstractConstraintLiteral<?> constraintLiteral, List<PreField> preFields) {
		Field bytecodeLineField = (Field) bytecodeLineConstantTableAccessibleObject.accessibleObject;

		if (constraintLiteral.isFinishedType && bytecodeLineField.getAnnotation(Variable.class) == null) {
			bytecodeLineField.setAccessible(true);

			Object value;
			try {
				value = bytecodeLineField.get(this.store.get(0));
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not get field \"" + bytecodeLineField.getName() + "\" for value \"" + this.store.get(0) + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new IllegalArgumentException(message);
			}

			if (CompareUtils.equalsAny(bytecodeLineField.getType(), CompareUtils.doubleClasses))
				return new AbstractConstraintLiteralDouble((Double) value);
			else if (CompareUtils.equalsAny(bytecodeLineField.getType(), CompareUtils.floatClasses))
				return new AbstractConstraintLiteralFloat((Float) value);
			else if (CompareUtils.equalsAny(bytecodeLineField.getType(), CompareUtils.integerClasses))
				return new AbstractConstraintLiteralInteger((Integer) value);
			else
				return new AbstractConstraintLiteralObject(value);

		} else if (constraintLiteral instanceof AbstractConstraintLiteralField) {
			AbstractConstraintLiteralField constraintLiteralField = (AbstractConstraintLiteralField) constraintLiteral;

			List<PreField> newPreFields = new ArrayList<PreField>(constraintLiteralField.preFields);
			newPreFields.add(new PreField(constraintLiteralField.value, constraintLiteralField.constantTablePrefix,
					constraintLiteralField.fieldCode, constraintLiteralField.fieldCodeIndex, constraintLiteralField.preFields));

			preFields.add(new PreField(
					bytecodeLineField, constraintLiteralField.constantTablePrefix + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
					constraintLiteralField.fieldCode, constraintLiteralField.fieldCodeIndex, new ArrayList<PreField>(newPreFields)));

			return new AbstractConstraintLiteralField(
					bytecodeLineField, constraintLiteralField.constantTablePrefix + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
					constraintLiteralField.fieldCode, constraintLiteralField.fieldCodeIndex, newPreFields);

		} else if (constraintLiteral instanceof AbstractConstraintLiteralClass) {
			AbstractConstraintLiteralClass constraintLiteralClass = (AbstractConstraintLiteralClass) constraintLiteral;

			preFields.add(new PreField(
					bytecodeLineField, "v_" + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
					constraintLiteralClass.fieldCode, constraintLiteralClass.fieldCodeIndex, new ArrayList<PreField>()));

			return new AbstractConstraintLiteralField(
					bytecodeLineField, "v_" + bytecodeLineConstantTableAccessibleObject.constantTableIndex + "_",
					constraintLiteralClass.fieldCode, constraintLiteralClass.fieldCodeIndex, new ArrayList<PreField>());

		} else {
			String message = "could not access field \"" + bytecodeLineField.getName() +"\" on literal \"" + constraintLiteral + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new MissformattedBytecodeLineException(message);
		}
	}
	
	/**
	 * 
	 * @param bytecodeLineConstantTableAccessibleObject
	 * @param constraintLiteral
	 * @param preFields
	 * 
	 * @return
	 */
	private AbstractConstraintValue getStaticField(BytecodeLineConstantTableAccessibleObject bytecodeLineConstantTableAccessibleObject, AbstractConstraintLiteral<?> constraintLiteral, List<PreField> preFields) {
		Field bytecodeLineField = (Field) bytecodeLineConstantTableAccessibleObject.accessibleObject;
		
		/** non-variable static field */
		if (bytecodeLineField.getAnnotation(Variable.class) == null) {
			bytecodeLineField.setAccessible(true);
			try {
				if (CompareUtils.equalsAny(bytecodeLineField.getType(), CompareUtils.doubleClasses))
					return new AbstractConstraintLiteralDouble(
							(Double) bytecodeLineField.get(null));
				else if (CompareUtils.equalsAny(bytecodeLineField.getType(), CompareUtils.floatClasses))
					return new AbstractConstraintLiteralFloat(
							(Float) bytecodeLineField.get(null));
				else if (CompareUtils.equalsAny(bytecodeLineField.getType(), CompareUtils.integerClasses))
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
			return this.getField(bytecodeLineConstantTableAccessibleObject, constraintLiteral, preFields);
	}
	
	/**
	 * 
	 * @param accessibleObject
	 * 
	 * @return
	 */
	private ArgumentList getArgumentList(AccessibleObject accessibleObject) {
		/** get count of parameters */
		int parameterCount = 0;
		if (accessibleObject instanceof Method)
			parameterCount = ((Method)accessibleObject).getParameterTypes().length;
		else if (accessibleObject instanceof Constructor<?>)
			parameterCount = ((Constructor<?>)accessibleObject).getParameterTypes().length;
		else {
			String message = "accessible object needs to be method or constructor but is \"" + accessibleObject.getClass().getName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
		
		/** pop argument values from stack */
		ArgumentList argumentValues = new ArgumentList();
		for (int i=0; i<parameterCount; i++) {
			AbstractConstraintValue argument = this.stack.pop();
			if (!argumentValues.hasPrematureArgument
					&& (!(argument instanceof AbstractConstraintLiteral)
							|| !((AbstractConstraintLiteral<?>)argument).isFinishedType))
				argumentValues.hasPrematureArgument = true;
			argumentValues.add(argument);
		}
		Collections.reverse(argumentValues);
		
		return argumentValues;
	}

	/**
	 * 
	 * @author Max Nitze
	 */
	private class ArgumentList extends ArrayList<AbstractConstraintValue> {
		/**  */
		private static final long serialVersionUID = 4116003574027287498L;

		/**  */
		public boolean hasPrematureArgument;

		/**
		 * 
		 */
		public ArgumentList() {
			super();
			this.hasPrematureArgument = false;
		}
	}
}
