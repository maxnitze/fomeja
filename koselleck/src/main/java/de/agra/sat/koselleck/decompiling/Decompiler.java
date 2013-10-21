package de.agra.sat.koselleck.decompiling;

/** imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintValue;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.ArithmeticOperator;
import de.agra.sat.koselleck.decompiling.datatypes.BooleanConnector;
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintOperator;
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintValueType;
import de.agra.sat.koselleck.decompiling.datatypes.PrefixedField;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;
import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.exceptions.UnknownOpcodeException;
import de.agra.sat.koselleck.exceptions.UnknownSwitchCaseException;

/**
 * 
 * @author Max Nitze
 */
public class Decompiler {
	/**  */
	private final Map<Integer, BytecodeLine> bytecodeLines;
	/**  */
	private final Stack<AbstractConstraintValue> stack;
	/**  */
	private final Map<Integer, AbstractConstraintValue> store;
	
	/**
	 * 
	 * @param bytecodeLines
	 */
	private Decompiler(Map<Integer, BytecodeLine> bytecodeLines) {
		this.bytecodeLines = bytecodeLines;
		
		this.stack = new Stack<AbstractConstraintValue>();
		this.store = new HashMap<Integer, AbstractConstraintValue>();
	}
	
	/**
	 * 
	 * @return
	 */
	private AbstractConstraint decompile() {
		this.stack.clear();
		this.store.clear();
		
		return getConstraint(0);
	}
	
	/** static methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param disassembledMethod
	 * 
	 * @return
	 */
	public static AbstractConstraint decompile(DisassembledMethod disassembledMethod) {
		Decompiler decompiler = new Decompiler(disassembledMethod.bytecodeLines);
		return decompiler.decompile();
	}
	
	/** constraint value methods
	 * ----- ----- ----- ----- ----- */
	
	private AbstractConstraint getConstraint(int offset) {
		BytecodeLine bytecodeLine = this.bytecodeLines.get(offset);
		int nextOffset = bytecodeLine.followingLineNumber;
		
		List<PrefixedField> prefixedFields = new ArrayList<PrefixedField>();
		
		Field field = null;
		PrefixedField prefixedField = null;
		
		AbstractConstraintValue constraintValue = null;
		AbstractConstraintLiteral constraintLiteral = null;
		AbstractConstraintValue constraintValue1 = null;
		AbstractConstraintValue constraintValue2 = null;
		
		Opcode fieldCode = null;
		int value = 0;
		StringBuilder fieldname = null;
		List<PrefixedField> preFields = null;
		
		do {
			nextOffset = bytecodeLine.followingLineNumber;
			
			switch(bytecodeLine.opcode) {
			case aload_0:
			case aload:
				fieldCode = bytecodeLine.opcode;
				value = bytecodeLine.value;
				fieldname = new StringBuilder("v");
				preFields = new ArrayList<PrefixedField>();
				prefixedField = null;
				break;
				
			case iconst:
			case bipush:
				this.stack.push(new AbstractConstraintLiteral(bytecodeLine.value, ConstraintValueType.INTEGER, false));
				break;
				
			case getfield:
				field = (Field)bytecodeLine.type.accessibleObject;
				fieldname.append(bytecodeLine.constantTableIndex);
				fieldname.append("_");
				if(prefixedField != null) {
					preFields.add(prefixedField);
					this.stack.pop();
				}
				
				prefixedField = new PrefixedField(field, bytecodeLine.type.accessibleObjectType, fieldCode, value, preFields, fieldname.toString());
				
				preFields = new ArrayList<PrefixedField>(preFields);
				prefixedFields.add(prefixedField);
				this.stack.push(new AbstractConstraintLiteral(prefixedField, ConstraintValueType.PREFIXED_FIELD, prefixedField.isVariable));
				break;
			case getstatic:
				field = (Field)bytecodeLine.type.accessibleObject;
				fieldname.append(bytecodeLine.constantTableIndex);
				fieldname.append("_");
				if(prefixedField != null) {
					preFields.add(prefixedField);
					this.stack.pop();
				}
				
				if(field.getAnnotation(Variable.class) != null) {
					prefixedField = new PrefixedField(field, bytecodeLine.type.accessibleObjectType, fieldCode, value, preFields, fieldname.toString());
					preFields = new ArrayList<PrefixedField>(preFields);
					prefixedFields.add(prefixedField);
					this.stack.push(new AbstractConstraintLiteral(prefixedField, ConstraintValueType.PREFIXED_FIELD, true));
				} else {
					field.setAccessible(true);
					try {
						this.stack.push(new AbstractConstraintLiteral(field.get(null), ConstraintValueType.fromClass(bytecodeLine.type.accessibleObjectType), false));
					} catch (IllegalArgumentException | IllegalAccessException e) {
						Logger.getLogger(Decompiler.class).fatal("could not access static field \"" + field.getName() +"\"");
						throw new IllegalArgumentException("could not access static field \"" + field.getName() +"\"");
					}
				}
				break;
				
			case checkcast:
				constraintValue = this.stack.pop();
				if(!(constraintValue instanceof AbstractConstraintLiteral)) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral.");
					throw new ClassCastException("could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral.");
				}
				
				constraintLiteral = (AbstractConstraintLiteral)constraintValue;
				if(constraintLiteral.valueType != ConstraintValueType.PREFIXED_FIELD) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintLiteral + "\" to \"" + bytecodeLine.type.clazz.getSimpleName() + "\"");
					throw new ClassCastException("could not cast given value \"" + constraintLiteral + "\" to \"" + bytecodeLine.type.clazz.getSimpleName() + "\"");
				}
				
				Field cField = ((PrefixedField)constraintLiteral.value).field;
				if(!cField.getType().isAssignableFrom(bytecodeLine.type.clazz)) {
					Logger.getLogger(Decompiler.class).fatal("could not cast from \"" + cField.getType().getSimpleName() + "\" to \"" + bytecodeLine.type.clazz.getSimpleName() + "\"");
					throw new ClassCastException("could not cast from \"" + cField.getType().getSimpleName() + "\" to \"" + bytecodeLine.type.clazz.getSimpleName() + "\"");
				}
				break;
				
			case add:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				this.stack.push(getCalculatedValue(constraintValue1, ArithmeticOperator.ADD, constraintValue2));
				break;
			case sub:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				this.stack.push(getCalculatedValue(constraintValue1, ArithmeticOperator.SUB, constraintValue2));
				break;
			case mul:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				this.stack.push(getCalculatedValue(constraintValue1, ArithmeticOperator.MUL, constraintValue2));
				break;
			case div:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				this.stack.push(getCalculatedValue(constraintValue1, ArithmeticOperator.DIV, constraintValue2));
				break;
				
			case tableswitch:
				constraintValue = this.stack.pop();
				if(!(constraintValue instanceof AbstractConstraintLiteral)) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral.");
					throw new ClassCastException("could not cast given value \"" + constraintLiteral + "\" to AbstractConstraintLiteral.");
				}
				
				constraintLiteral = (AbstractConstraintLiteral)constraintValue;
				if(constraintLiteral.valueType != ConstraintValueType.INTEGER) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintLiteral + "\" to integer.");
					throw new ClassCastException("could not cast given value \"" + constraintLiteral + "\" to integer.");
				}
				
				Integer caseOffset = bytecodeLine.switchOffsets.get(((Integer)constraintLiteral.value).toString());
				if(caseOffset == null) {
					caseOffset = bytecodeLine.switchOffsets.get("default");
					if(caseOffset == null) {
						String message = "no case for value \"" + ((Integer)constraintLiteral.value).toString() + "\" and no default case";
						Logger.getLogger(Decompiler.class).fatal(message);
						throw new UnknownSwitchCaseException(message);
					} else
						nextOffset = caseOffset;
				} else
					nextOffset = caseOffset;
				break;
				
			case _goto:
				nextOffset = bytecodeLine.offset;
				break;
				
			case iload:
				this.stack.push(this.store.get(bytecodeLine.value));
				break;
				
			case istore:
				this.store.put(bytecodeLine.value, this.stack.pop());
				break;
			
			case ifeq:
				constraintValue = this.stack.pop();
				if(!(constraintValue instanceof AbstractConstraintLiteral)) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral.");
					throw new ClassCastException("could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral.");
				}
				
				constraintLiteral = (AbstractConstraintLiteral)constraintValue;
				if(constraintLiteral.valueType != ConstraintValueType.INTEGER) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintLiteral + "\" to integer.");
					throw new ClassCastException("could not cast given value \"" + constraintLiteral + "\" to integer.");
				}
				
				if((Integer)constraintLiteral.value == 0)
					nextOffset = bytecodeLine.offset;
				break;
			case ifne:
				constraintValue = this.stack.pop();
				if(!(constraintValue instanceof AbstractConstraintLiteral)) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintValue + "\" to AbstractConstraintLiteral.");
					throw new ClassCastException("could not cast given value \"" + constraintLiteral + "\" to AbstractConstraintLiteral.");
				}
				
				constraintLiteral = (AbstractConstraintLiteral)constraintValue;
				if(constraintLiteral.valueType != ConstraintValueType.INTEGER) {
					Logger.getLogger(Decompiler.class).fatal("could not cast given value \"" + constraintLiteral + "\" to integer.");
					throw new ClassCastException("could not cast given value \"" + constraintLiteral + "\" to integer.");
				}
				
				if((Integer)constraintLiteral.value != 0)
					nextOffset = bytecodeLine.offset;
				break;
				
			case if_icmpne:
			case if_icmpge:
			case if_icmpgt:
			case if_icmple:
			case if_icmplt:
			case if_icmpeq:
				constraintValue2 = this.stack.pop();
				constraintValue1 = this.stack.pop();
				
				return new AbstractSubConstraint(
						new AbstractSubConstraint(
								getSingleConstraint(constraintValue1, ConstraintOperator.fromOpcode(bytecodeLine.opcode), constraintValue2, prefixedFields),
								BooleanConnector.AND,
								getConstraint(bytecodeLine.offset)),
						BooleanConnector.OR,
						new AbstractSubConstraint(
								getSingleConstraint(constraintValue1, ConstraintOperator.fromOppositeOpcode(bytecodeLine.opcode), constraintValue2, prefixedFields),
								BooleanConnector.AND,
								getConstraint(bytecodeLine.followingLineNumber)));
				
			case ireturn:
				AbstractConstraintValue returnValue = this.stack.pop();
				if(!(returnValue instanceof AbstractConstraintLiteral)) {
					Logger.getLogger(Decompiler.class).fatal("could not return given value \"" + returnValue + "\" as integer.");
					throw new ClassCastException("could not return given value \"" + returnValue + "\" as integer.");
				}
				
				AbstractConstraintLiteral returnLiteral = (AbstractConstraintLiteral)returnValue;
				if(returnLiteral.valueType != ConstraintValueType.INTEGER) {
					Logger.getLogger(Decompiler.class).fatal("could not return given value \"" + returnLiteral + "\" as integer.");
					throw new ClassCastException("could not return given value \"" + returnLiteral + "\" as integer.");
				}
				
				return new AbstractBooleanConstraint(((Integer)returnLiteral.value).equals(1) ? true : false); 
				
			default:
				Logger.getLogger(Decompiler.class).fatal("Opcode " + (bytecodeLine.opcode == null ? "null" : "\"" + bytecodeLine.opcode.name + "\"") + " is not known");
				throw new UnknownOpcodeException(bytecodeLine.opcode);
			}
			
			bytecodeLine = this.bytecodeLines.get(nextOffset);
		} while(nextOffset > 0);
		
		return new AbstractBooleanConstraint(true);
	}
	
	/**
	 * 
	 * @param constraintValue1
	 * @param operator
	 * @param constraintValue2
	 * 
	 * @return
	 */
	private AbstractConstraintValue getCalculatedValue(AbstractConstraintValue constraintValue1, ArithmeticOperator operator, AbstractConstraintValue constraintValue2) {
		if(
				constraintValue1 instanceof AbstractConstraintLiteral &&
				constraintValue2 instanceof AbstractConstraintLiteral) {
			AbstractConstraintLiteral constraintLiteral1 = (AbstractConstraintLiteral)constraintValue1;
			AbstractConstraintLiteral constraintLiteral2 = (AbstractConstraintLiteral)constraintValue2;
			
			if(
					constraintLiteral1.valueType == ConstraintValueType.INTEGER &&
					constraintLiteral2.valueType == ConstraintValueType.INTEGER) {
				switch(operator) {
				case ADD:
					return new AbstractConstraintLiteral(((Integer)constraintLiteral1.value).intValue() + ((Integer)constraintLiteral2.value).intValue(), ConstraintValueType.INTEGER, false);
				case SUB:
					return new AbstractConstraintLiteral(((Integer)constraintLiteral1.value).intValue() - ((Integer)constraintLiteral2.value).intValue(), ConstraintValueType.INTEGER, false);
				case MUL:
					return new AbstractConstraintLiteral(((Integer)constraintLiteral1.value).intValue() * ((Integer)constraintLiteral2.value).intValue(), ConstraintValueType.INTEGER, false);
				case DIV:
					return new AbstractConstraintLiteral(((Integer)constraintLiteral1.value).intValue() / ((Integer)constraintLiteral2.value).intValue(), ConstraintValueType.INTEGER, false);
				default:
					Logger.getLogger(Decompiler.class).fatal("ArithmeticOperator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
					throw new UnknownArithmeticOperatorException(operator);
				}
			} else
				return new AbstractConstraintFormula(
						constraintValue1,
						operator,
						constraintValue2);
		} else
			return new AbstractConstraintFormula(
					constraintValue1,
					operator,
					constraintValue2);
	}
	
	/**
	 * 
	 * @param constraintValue1
	 * @param constraintOperator
	 * @param constraintValue2
	 * @param prefixedFields
	 * 
	 * @return
	 */
	private AbstractConstraint getSingleConstraint(AbstractConstraintValue constraintValue1, ConstraintOperator constraintOperator, AbstractConstraintValue constraintValue2, List<PrefixedField> prefixedFields) {
		if(
				constraintValue1 instanceof AbstractConstraintLiteral &&
				constraintValue2 instanceof AbstractConstraintLiteral) {
			AbstractConstraintLiteral constraintLiteral1 = (AbstractConstraintLiteral)constraintValue1;
			AbstractConstraintLiteral constraintLiteral2 = (AbstractConstraintLiteral)constraintValue2;
			
			if(
					constraintLiteral1.valueType == ConstraintValueType.INTEGER &&
					constraintLiteral2.valueType == ConstraintValueType.INTEGER) {
				Integer value1 = (Integer)constraintLiteral1.value;
				Integer value2 = (Integer)constraintLiteral2.value;
				
				switch(constraintOperator) {
				case EQUAL:
					return new AbstractBooleanConstraint(value1.compareTo(value2) == 0);
				case GREATER:
					return new AbstractBooleanConstraint(value1.compareTo(value2) > 0);
				case GREATER_EQUAL:
					return new AbstractBooleanConstraint(value1.compareTo(value2) >= 0);
				case LESS:
					return new AbstractBooleanConstraint(value1.compareTo(value2) < 0);
				case LESS_EQUAL:
					return new AbstractBooleanConstraint(value1.compareTo(value2) <= 0);
				case NOT_EQUAL:
					return new AbstractBooleanConstraint(value1.compareTo(value2) != 0);
				default:
					Logger.getLogger(Decompiler.class).fatal("constraint operator " + (constraintOperator == null ? "null" : "\"" + constraintOperator.asciiName + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(constraintOperator);
				}
			} else
				return new AbstractSingleConstraint(
						constraintValue1,
						constraintOperator,
						constraintValue2,
						prefixedFields);
		} else
			return new AbstractSingleConstraint(
					constraintValue1,
					constraintOperator,
					constraintValue2,
					prefixedFields);
	}
}
