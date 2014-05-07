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

import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineConstantTableAccessibleObject;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineConstantTableClass;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineOffset;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineSimple;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineTableswitch;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineValue;
import de.agra.sat.koselleck.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;
import de.agra.sat.koselleck.types.Opcode;

/**
 * Disassembler implements a disassembler for java byte code.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Disassembler {
	/**  */
	private static final Pattern simpleTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleTypeGroup() + ")$");
	/**  */
	private static final Pattern valueTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleValueTypeGroup() + ")(?<value>[+-]?[0-9]+(\\.[0-9]+)?)$");
	/**  */
	private static final Pattern constantTableValueTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableValueTypeGroup() + ") #\\d+ // (float|double) (?<value>[+-]?[0-9]+(\\.[0-9]+)?)(?<valuetype>[f|d])$");
	/**  */
	private static final Pattern offsetTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$");
	/**  */
	private static final Pattern constantTableAccessibleObjectTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) // (?<accessibleobjecttype>Field|Method) (?<accessibleobject>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$");
	/**  */
	private static final Pattern constantTableClassTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) // class (?<class>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$"); // TODO might not be right
	/**  */
	private static final Pattern tableswitchPattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantSwitchGroup() + ") \\{ // \\d+ to \\d+$");
	/**  */
	private static final Pattern tableswitchCasePattern =
			Pattern.compile("^(?<case>(\\d+|default)): (?<offset>\\d+)$");

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
		System.out.println(this.disassembledMethodString); // TODO delete output disassembledMethodString

		/** bytecode lines to return */
		Map<Integer, BytecodeLine> bytecodeLines = new HashMap<Integer, BytecodeLine>();

		String[] disassembledMethodLines = this.disassembledMethodString.split("\n");
		for(int i=0; i<disassembledMethodLines.length; i++) {
			String disassembledMethodLine = disassembledMethodLines[i].trim().replaceAll("\\s+", " ");

			/** is simple bytecode line */
			if(disassembledMethodLine.matches(simpleTypePattern.pattern())) {
				Matcher matcher = simpleTypePattern.matcher(disassembledMethodLine);
				matcher.find();

				int lineNumber = Integer.parseInt(matcher.group("number"));

				bytecodeLines.put(lineNumber, new BytecodeLineSimple(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode"))));
			}
			/** is value bytecode line */
			else if(disassembledMethodLine.matches(valueTypePattern.pattern())) {
				Matcher matcher = valueTypePattern.matcher(disassembledMethodLine);
				matcher.find();

				int lineNumber = Integer.parseInt(matcher.group("number"));
				String opcodeString = matcher.group("opcode").trim();
				String valueString = matcher.group("value");

				Object value;
				if(valueString.matches("^[+-]?[0-9]+(\\.[0-9]+)?$")) {
					if(opcodeString.startsWith("f"))
						value = Float.parseFloat(valueString);
					else if(opcodeString.startsWith("d"))
						value = Double.parseDouble(valueString);
					else
						value = Integer.parseInt(valueString);
				} else
					value = valueString;

				bytecodeLines.put(lineNumber, new BytecodeLineValue(
						disassembledMethodLine, lineNumber, Opcode.fromString(opcodeString), value));
			}
			/** is offset bytecode line */
			else if(disassembledMethodLine.matches(constantTableValueTypePattern.pattern())) {
				Matcher matcher = constantTableValueTypePattern.matcher(disassembledMethodLine);
				matcher.find();

				int lineNumber = Integer.parseInt(matcher.group("number"));
				String valueTypeString = matcher.group("valuetype");

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
			else if(disassembledMethodLine.matches(offsetTypePattern.pattern())) {
				Matcher matcher = offsetTypePattern.matcher(disassembledMethodLine);
				matcher.find();

				int lineNumber = Integer.parseInt(matcher.group("number"));

				bytecodeLines.put(lineNumber, new BytecodeLineOffset(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode")),
						Integer.parseInt(matcher.group("offset"))));
			}
			/** is constant table class bytecode line */
			else if(disassembledMethodLine.matches(constantTableClassTypePattern.pattern())) {
				Matcher matcher = constantTableClassTypePattern.matcher(disassembledMethodLine);
				matcher.find();

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
			else if(disassembledMethodLine.matches(constantTableAccessibleObjectTypePattern.pattern())) {
				Matcher matcher = constantTableAccessibleObjectTypePattern.matcher(disassembledMethodLine);
				matcher.find();

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
					List<Class<?>> parameterTypesList = new ArrayList<Class<?>>();
					if(matcher.group("parametertypes") != null) {
						String[] parameterTypes = matcher.group("parametertypes").split(";");
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
			/** is tableswitch bytecode line */
			else if(disassembledMethodLine.matches(tableswitchPattern.pattern())) {
				Matcher matcher = tableswitchPattern.matcher(disassembledMethodLine);
				matcher.find();

				int lineNumber = Integer.parseInt(matcher.group("number"));

				BytecodeLineTableswitch bytecodeLineTableSwitch = new BytecodeLineTableswitch(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(matcher.group("opcode")));

				while(i+1<disassembledMethodLines.length && disassembledMethodLines[i+1].matches(tableswitchCasePattern.pattern())) {
					++i;

					bytecodeLineTableSwitch.offsetsMap.put(
							disassembledMethodLines[i].replaceAll(tableswitchCasePattern.pattern(), "${case}"),
							Integer.parseInt(disassembledMethodLines[i].replaceAll(tableswitchCasePattern.pattern(), "${offset}")));
				}

				bytecodeLines.put(lineNumber, bytecodeLineTableSwitch);
			}
			/** otherwise */
			else {
				String message = "could not parse given bytecode line \"" + disassembledMethodLine + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new MissformattedBytecodeLineException(message);
			}
		}

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
