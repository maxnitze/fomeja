package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineConstantTableAccessibleObject;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineConstantTableClass;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineOffset;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineSimple;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineValue;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;
import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;

/**
 * Disassembler implements a disassembler for java byte code.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Disassembler {
	/**  */
	private final Pattern simpleTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleTypeGroup() + ")$");
//	/**  */
//	private final Pattern simpleValueTypePattern =
//			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleValueTypeGroup() + ")_(?<value>\\d+)$");
	/**  */
	private final Pattern valueTypePattern =
			Pattern.compile("^(?<number>\\d+): ((?<opcode>" + Opcode.getValueTypeGroup() + ") |(?<opcode>" + Opcode.getSimpleTypeGroup() + ")_)(?<value>\\d+)$");
	/**  */
	private final Pattern constantTableValueTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableValueTypeGroup() + ") #\\d+ // (float|double) (?<value>\\d+)(?<valuetype>[f|d])$");
	/**  */
	private final Pattern offsetTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$");
	/**  */
	private final Pattern constantTableAccessibleObjectTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) // (?<accessibleobjecttype>Field|Method) (?<accessibleobject>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$");
	/**  */
	private final Pattern constantTableClassTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) // class (?<class>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$"); // TODO might not be right
	
	/** the component */
	private final Class<?> componentClass;
	/** the method to disassemble */
	private final Method method;
	/** the signature of the method */
	private final String methodSignature;
	/** the java byte code of the method */
	private final String disassembledMethodString;
	
	/**
	 * Constructor for a new disassembler.
	 * 
	 * @param componentClass the class of the new component
	 * @param method the new method
	 * @param methodSignature the new method signature
	 * @param disassembledMethodString the new java byte code of the method
	 */
	private Disassembler(Class<?> componentClass, Method method, String methodSignature, String disassembledMethodString) {
		this.componentClass = componentClass;
		this.method = method;
		this.methodSignature = methodSignature;
		this.disassembledMethodString = disassembledMethodString;
	}
	
	/**
	 * disassemble splits the disassembled method into its lines and returns a
	 *  disassembled method with a map of the single byte code lines.
	 * 
	 * @return a disassembled method with a map of the single byte code lines
	 */
	private DisassembledMethod disassemble() {
		System.out.println(this.disassembledMethodString); // TODO delete print line
		
		/** bytecode lines to return */
		Map<Integer, BytecodeLine> bytecodeLines = new HashMap<Integer, BytecodeLine>();
		
		String[] disassembledMethodLines = this.disassembledMethodString.split("\n");
		for(int i=0; i<disassembledMethodLines.length; i++) {
			String disassembledMethodLine = disassembledMethodLines[i].trim().replaceAll("\\s+", " ");
			
			/** is simple bytecode line */
			if(disassembledMethodLine.matches(this.simpleTypePattern.pattern())) {
				Matcher matcher = this.simpleTypePattern.matcher(disassembledMethodLine);
				
				int lineNumber = Integer.parseInt(matcher.group("number"));
				
				bytecodeLines.put(lineNumber, new BytecodeLineSimple(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode"))));
			}
			/** is value bytecode line */
			else if(disassembledMethodLine.matches(this.valueTypePattern.pattern())) {
				Matcher matcher = this.valueTypePattern.matcher(disassembledMethodLine);
				
				int lineNumber = Integer.parseInt(matcher.group("number"));
				String opcodeString = matcher.group("opcode");
				String valueString = matcher.group("value");
				
				Object value;
				if(valueString.matches("^\\d+$")) {
					if(opcodeString.startsWith("i"))
						value = Integer.parseInt(valueString);
					else if(opcodeString.startsWith("f"))
						value = Float.parseFloat(valueString);
					else if(opcodeString.startsWith("d"))
						value = Double.parseDouble(valueString);
					else
						value = valueString;
				} else
					value = valueString;
				
				bytecodeLines.put(lineNumber, new BytecodeLineValue(
						disassembledMethodLine, lineNumber, Opcode.fromString(opcodeString), value));
			}
			/** is offset bytecode line */
			else if(disassembledMethodLine.matches(this.constantTableValueTypePattern.pattern())) {
				Matcher matcher = this.constantTableValueTypePattern.matcher(disassembledMethodLine);
				
				int lineNumber = Integer.parseInt(matcher.group("number"));
				String valueTypeString = matcher.group("valueType");
				
				Object value;
				if(valueTypeString.equals("f"))
					value = Float.parseFloat(matcher.group("value"));
				else if(valueTypeString.equals("d"))
					value = Double.parseDouble(matcher.group("value"));
				else
					value = matcher.group("value");
				
				bytecodeLines.put(lineNumber, new BytecodeLineValue(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode")), value));
			}
			/** is offset bytecode line */
			else if(disassembledMethodLine.matches(this.offsetTypePattern.pattern())) {
				Matcher matcher = this.offsetTypePattern.matcher(disassembledMethodLine);
				
				int lineNumber = Integer.parseInt(matcher.group("number"));
				
				bytecodeLines.put(lineNumber, new BytecodeLineOffset(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode")),
						Integer.parseInt(matcher.group("offset"))));
			}
			/** is constant table class bytecode line */
			else if(disassembledMethodLine.matches(this.constantTableClassTypePattern.pattern())) {
				Matcher matcher = this.constantTableClassTypePattern.matcher(disassembledMethodLine);
				
				int lineNumber = Integer.parseInt(matcher.group("number"));
				
				Class<?> clazz;
				try {
					clazz = Class.forName(matcher.group("class"));
				} catch (ClassNotFoundException e) {
					String message = "";
					Logger.getLogger(Disassembler.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}
				
				bytecodeLines.put(lineNumber, new BytecodeLineConstantTableClass(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode")),
						Integer.parseInt(matcher.group("index")), clazz));
			}
			/** is constant table accessible object bytecode line */
			else if(disassembledMethodLine.matches(this.constantTableAccessibleObjectTypePattern.pattern())) {
				Matcher matcher = this.constantTableAccessibleObjectTypePattern.matcher(disassembledMethodLine);
				
				int lineNumber = Integer.parseInt(matcher.group("number"));
				
				String accessibleObjectType = matcher.group("accessibleobjecttype");
				
				/** accessible object is a field */
				if(accessibleObjectType.equals("Field")) {
					String fieldString = matcher.group("accessibleobject");
					Class<?> fieldClass;
					String fieldName;
					if(fieldString.contains(".")) {
						String[] splittedField = fieldString.split("\\.");
						String className = splittedField[0].replaceAll("/", ".");
						try {
							fieldClass = Class.forName(className);
						} catch (ClassNotFoundException e) {
							String message = "could not find class for name \"" + className + "\"";
							Logger.getLogger(Disassembler.class).fatal(message);
							throw new MissformattedBytecodeLineException(message);
						}
						fieldName = splittedField[1];
					} else {
						fieldClass = this.componentClass;
						fieldName = fieldString;
					}
					
					AccessibleObject object;
					try {
						object = fieldClass.getDeclaredField(fieldName);
					} catch (NoSuchFieldException | SecurityException e) {
						String message = "could not find field \"" + fieldName + "\" for class \"" + fieldClass.getCanonicalName() + "\"";
						Logger.getLogger(Disassembler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					}
					
					bytecodeLines.put(lineNumber, new BytecodeLineConstantTableAccessibleObject(
							disassembledMethodLine, lineNumber,
							Opcode.fromString(matcher.group("opcode")),
							Integer.parseInt(matcher.group("index")), object));
				}
				/** accessible object is a method */
				else if(accessibleObjectType.equals("Method")) {
					String methodString = matcher.group("accessibleobject");
					Class<?> methodClass;
					String methodName;
					if(methodString.contains(".")) {
						String[] splittedField = methodString.split("\\.");
						String className = splittedField[0].replaceAll("/", ".");
						try {
							methodClass = Class.forName(className);
						} catch (ClassNotFoundException e) {
							String message = "could not find class for name \"" + className + "\"";
							Logger.getLogger(Disassembler.class).fatal(message);
							throw new MissformattedBytecodeLineException(message);
						}
						methodName = splittedField[1];
					} else {
						methodClass = this.componentClass;
						methodName = methodString;
					}
					
					/** get parameter types */
					String[] parameterTypes = matcher.group("parameterTypes").split(";");
					List<Class<?>> parameterTypesList = new ArrayList<Class<?>>();
					for(String paramType : parameterTypes) {
						String parameterTypeClassName = paramType.replaceAll("/", ".");
						if(parameterTypeClassName == null || parameterTypeClassName.equals(""))
							continue;
						else if(parameterTypeClassName.equals("D"))
							parameterTypesList.add(double.class);
						else if(parameterTypeClassName.equals("F"))
							parameterTypesList.add(float.class);
						else if(parameterTypeClassName.equals("I"))
							parameterTypesList.add(int.class);
						else {
							try {
								parameterTypeClassName = parameterTypeClassName.substring(1);
								parameterTypesList.add(Class.forName(parameterTypeClassName));
							} catch (ClassNotFoundException e) {
								String message = "could not find class for name \"" + parameterTypeClassName + "\"";
								Logger.getLogger(Disassembler.class).fatal(message);
								throw new MissformattedBytecodeLineException(message);
							}
						}
					}
					
					AccessibleObject object;
					try {
						if(methodName.equals("\"<init>\""))
							object = methodClass.getDeclaredConstructor(parameterTypesList.toArray(new Class[parameterTypesList.size()]));
						else
							object = methodClass.getDeclaredMethod(methodName, parameterTypesList.toArray(new Class[parameterTypesList.size()]));
					} catch (NoSuchMethodException | SecurityException e) {
						StringBuilder parameterString = new StringBuilder();
						for(Class<?> cls : parameterTypesList) {
							if(parameterString.length() > 0)
								parameterString.append(", ");
							parameterString.append(cls.getCanonicalName());
						}
						
						String message;
						if(methodName.equals("\"<init>\""))
							message = "could not find constructor with parameters \"(" + parameterString.toString() + ")\" for class \"" + methodClass.getCanonicalName() + "\"";
						else
							message = "could not find method \"" + methodName + "(" + parameterString.toString() + ")\" for class \"" + methodClass.getCanonicalName() + "\"";
						Logger.getLogger(Disassembler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					}
					
					bytecodeLines.put(lineNumber, new BytecodeLineConstantTableAccessibleObject(
							disassembledMethodLine, lineNumber,
							Opcode.fromString(matcher.group("opcode")),
							Integer.parseInt(matcher.group("index")), object));
				}
			}
			/** otherwise */
			else {
				String message = "could not parse given bytecode line \"" + disassembledMethodLine + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new MissformattedBytecodeLineException(message);
			}
		}
		
//		String[] methodLines = this.disassembledMethodString.split("\n");
//		for(int i=0; i<methodLines.length; i++) {
//			BytecodeLine bytecodeLine = new BytecodeLine(this.componentClass, methodLines[i]);
//			bytecodeLines.put(bytecodeLine.lineNumber, bytecodeLine);
//			if(bytecodeLine.opcode == Opcode.tableswitch)
//				while(methodLines[i+1].matches(BytecodeLineRegexes.switchCase))
//					bytecodeLine.switchOffsets.put(
//							methodLines[++i].replaceAll(BytecodeLineRegexes.switchCase, "${case}"),
//							Integer.parseInt(methodLines[i].replaceAll(BytecodeLineRegexes.switchCase, "${offset}")));
//		}
		
		return new DisassembledMethod(this.method, this.methodSignature, this.disassembledMethodString, bytecodeLines);
	}
	
	/** static methods
	 * ----- ----- ----- ----- */
	
	/**
	 * disassemble instantiates a new disassembler with the given method and
	 *  returns the disassembled method.
	 * 
	 * @param componentClass the class of the component for the method
	 * @param methodSignature the signature of the method
	 * @param disassembledMethod the disassembled method
	 * 
	 * @return the disassembled method object of the given method
	 */
	public static DisassembledMethod disassemble(Class<?> componentClass, Method method, String methodSignature, String disassembledMethod) {
		Disassembler disassembler = new Disassembler(componentClass, method, methodSignature, disassembledMethod);
		return disassembler.disassemble();
	}
}
