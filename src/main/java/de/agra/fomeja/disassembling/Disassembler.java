package de.agra.fomeja.disassembling;

/* imports */
import java.io.IOException;
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLine;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineConstantTableAccessibleObject;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineConstantTableClass;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineMultipleValue;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineOffset;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineSimple;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineSimpleValue;
import de.agra.fomeja.disassembling.bytecodetypes.BytecodeLineTableswitch;
import de.agra.fomeja.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.fomeja.exceptions.DisassemblerException;
import de.agra.fomeja.types.Opcode;
import de.agra.fomeja.utils.IOUtils;
import de.agra.fomeja.utils.RefactoringUtils;

/**
 * Disassembler implements a disassembler for java byte code.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Disassembler {
	/** COMMENT */
	private static final String startingPattern = "^(?<number>\\d+): (?<opcode>";
	/** COMMENT */
	private static final Pattern simpleTypePattern =
			Pattern.compile(startingPattern + Opcode.simpleTypeGroup + ")$");
	/** COMMENT */
	private static final Pattern simpleValueTypePattern =
			Pattern.compile(startingPattern + Opcode.simpleValueTypeGroup + ")(\\s+)?(?<value>(([+-]?[0-9]+(\\.[0-9]+)?)|(boolean|byte|char|double|int|float|long|short)))$");
	/** COMMENT */
	private static final Pattern multipleValueTypePattern =
			Pattern.compile(startingPattern + Opcode.multipleValueTypeGroup + ") (?<values>[+-]?[0-9]+(\\.[0-9]+)?(, [+-]?[0-9]+(\\.[0-9]+)?)+)$");
	/** COMMENT */
	private static final Pattern constantTableValueTypePattern =
			Pattern.compile(startingPattern + Opcode.constantTableValueTypeGroup + ") #\\d+ // (?<type>float|double|String) (?<value>([+-]?[0-9]+(\\.[0-9]+)?)(?<valuetype>[f|d])|(.*))$");
	/** COMMENT */
	private static final Pattern offsetTypePattern =
			Pattern.compile(startingPattern + Opcode.offsetTypeGroup + ") (?<offset>\\d+)$");
	/** COMMENT */
	private static final Pattern constantTableAccessibleObjectTypePattern =
			Pattern.compile(startingPattern + Opcode.constantTableIndexTypeGroup + ") #(?<index>\\d+) // (?<accessibleobjecttype>Field|Method) (?<accessibleobject>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$");
	/** COMMENT */
	private static final Pattern constantTableClassTypePattern =
			Pattern.compile(startingPattern + Opcode.constantTableIndexTypeGroup + ") #(?<index>\\d+) // class (?<class>\\S+)(:(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+))?$");
	/** COMMENT */
	private static final Pattern tableswitchPattern =
			Pattern.compile(startingPattern + Opcode.switchTypeGroup + ") \\{ // \\d+ to \\d+$");
	/** COMMENT */
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

	private Map<Integer, BytecodeLine> bytecodeLines;

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
		this.bytecodeLines = new HashMap<Integer, BytecodeLine>();

		String[] disassembledMethodLines = this.disassembledMethodString.split("\n");
		for (int i=0; i<disassembledMethodLines.length; i++) {
			String disassembledMethodLine = disassembledMethodLines[i].trim().replaceAll("\\s+", " ");

			/** is simple bytecode line */
			if (disassembledMethodLine.matches(simpleTypePattern.pattern()))
				this.parseSimpleType(disassembledMethodLine);
			/** is simple value bytecode line */
			else if (disassembledMethodLine.matches(simpleValueTypePattern.pattern()))
				this.parseSimpleValueType(disassembledMethodLine);
			/** is multiple value bytecode line */
			else if (disassembledMethodLine.matches(multipleValueTypePattern.pattern()))
				this.parseMultipleValueType(disassembledMethodLine);
			/** is constant table value bytecode line */
			else if (disassembledMethodLine.matches(constantTableValueTypePattern.pattern()))
				this.parseConstantTableValueType(disassembledMethodLine);
			/** is offset bytecode line */
			else if (disassembledMethodLine.matches(offsetTypePattern.pattern()))
				this.parseOffsetType(disassembledMethodLine);
			/** is constant table class bytecode line */
			else if (disassembledMethodLine.matches(constantTableClassTypePattern.pattern()))
				this.parseConstantTableClassType(disassembledMethodLine);
			/** is constant table accessible object bytecode line */
			else if (disassembledMethodLine.matches(constantTableAccessibleObjectTypePattern.pattern()))
				this.parseConstantTableAccessibleObjectType(disassembledMethodLine);
			/** is tableswitch bytecode line */
			else if (disassembledMethodLine.matches(tableswitchPattern.pattern()))
				i += this.parseTableswitch(disassembledMethodLine, disassembledMethodLines, i);
			/** otherwise */
			else {
				String message = "could not parse given bytecode line \"" + disassembledMethodLine + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
			}
		}

		return new DisassembledMethod(this.method, this.methodSignature, this.disassembledMethodString, bytecodeLines);
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseSimpleType(String line) {
		Matcher matcher = simpleTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
	
			this.bytecodeLines.put(lineNumber, new BytecodeLineSimple(
					line, lineNumber, Opcode.fromString(matcher.group("opcode"))));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseSimpleValueType(String line) {
		Matcher matcher = simpleValueTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
			String opcodeString = matcher.group("opcode").trim();
			String valueString = matcher.group("value");
	
			Object value;
			if (valueString.matches("^[+-]?[0-9]+(\\.[0-9]+)?$")) {
				if (opcodeString.startsWith("f"))
					value = Float.parseFloat(valueString);
				else if (opcodeString.startsWith("d"))
					value = Double.parseDouble(valueString);
				else
					value = Integer.parseInt(valueString);
			} else if (valueString.equals("boolean"))
				value = boolean.class;
			else if (valueString.equals("byte"))
				value = byte.class;
			else if (valueString.equals("char"))
				value = char.class;
			else if (valueString.equals("double"))
				value = double.class;
			else if (valueString.equals("float"))
				value = float.class;
			else if (valueString.equals("int"))
				value = int.class;
			else if (valueString.equals("long"))
				value = long.class;
			else if (valueString.equals("short"))
				value = short.class;
			else
				value = valueString;
	
			this.bytecodeLines.put(lineNumber, new BytecodeLineSimpleValue(
					line, lineNumber, Opcode.fromString(opcodeString), value));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseMultipleValueType(String line) {
		Matcher matcher = multipleValueTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
			String opcodeString = matcher.group("opcode").trim();
			String valuesString = matcher.group("values");
	
			String[] splittedValues = valuesString.split(",");
			Object[] values = new Object[splittedValues.length];
			for (int i=0; i<splittedValues.length; i++) {
				String splittedValue = splittedValues[i].trim();
				if (splittedValue.matches("^[+-]?[0-9]+(\\.[0-9]+)?[df]?$")) {
					if (splittedValue.endsWith("f"))
						values[i] = Float.parseFloat(splittedValue);
					else if (splittedValue.endsWith("d"))
						values[i] = Double.parseDouble(splittedValue);
					else
						values[i] = Integer.parseInt(splittedValue);
				} else
					values[i] = splittedValue;
			}
	
			this.bytecodeLines.put(lineNumber, new BytecodeLineMultipleValue(
					line, lineNumber, Opcode.fromString(opcodeString), values));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseConstantTableValueType(String line) {
		Matcher matcher = constantTableValueTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
			String type = matcher.group("type");
	
			Object value;
			if (type.equals("float"))
				value = Float.parseFloat(matcher.group("value"));
			else if (type.equals("double"))
				value = Double.parseDouble(matcher.group("value"));
			else if (type.equals("String"))
				value = new String(matcher.group("value"));
			else {
				String message = "could not parse given line \"" + line + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
			}
	
			this.bytecodeLines.put(lineNumber, new BytecodeLineSimpleValue(
					line, lineNumber, Opcode.fromString(matcher.group("opcode")), value));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseOffsetType(String line) {
		Matcher matcher = offsetTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
	
			this.bytecodeLines.put(lineNumber, new BytecodeLineOffset(
					line, lineNumber, Opcode.fromString(matcher.group("opcode")),
					Integer.parseInt(matcher.group("offset"))));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseConstantTableClassType(String line) {
		Matcher matcher = constantTableClassTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
			String className = matcher.group("class").replaceAll("/", ".");

			Class<?> clazz;
			try {
				clazz = Class.forName(className);
			} catch (ClassNotFoundException e) {
				String message = "could not find class for name \"" + className + "\": " + e.getMessage();
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
			}
	
			this.bytecodeLines.put(lineNumber, new BytecodeLineConstantTableClass(
					line, lineNumber, Opcode.fromString(matcher.group("opcode")),
					Integer.parseInt(matcher.group("index")), clazz));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseConstantTableAccessibleObjectType(String line) {
		Matcher matcher = constantTableAccessibleObjectTypePattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
	
			String accessibleObjectType = matcher.group("accessibleobjecttype");
	
			/** accessible object is a field */
			if (accessibleObjectType.equals("Field"))
				this.parseConstantTableAccessibleObjectTypeField(line, matcher, lineNumber);
			/** accessible object is a method */
			else if (accessibleObjectType.equals("Method"))
				this.parseConstantTableAccessibleObjectTypeMethod(line, matcher, lineNumber);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 * @param matcher
	 * @param lineNumber
	 */
	private void parseConstantTableAccessibleObjectTypeField(String line, Matcher matcher, int lineNumber) {
		String fieldString = matcher.group("accessibleobject");
		Class<?> fieldClass;
		String fieldName;
		if (fieldString.contains(".")) {
			String[] splittedField = fieldString.split("\\.");
			String className = splittedField[0].replaceAll("/", ".");
			try {
				fieldClass = Class.forName(className);
			} catch (ClassNotFoundException e) {
				String message = "could not find class for name \"" + className + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
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
			throw new DisassemblerException(message);
		}

		this.bytecodeLines.put(lineNumber, new BytecodeLineConstantTableAccessibleObject(
				line, lineNumber, Opcode.fromString(matcher.group("opcode")),
				Integer.parseInt(matcher.group("index")), object));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 * @param matcher
	 * @param lineNumber
	 */
	private void parseConstantTableAccessibleObjectTypeMethod(String line, Matcher matcher, int lineNumber) {
		String methodString = matcher.group("accessibleobject");
		Class<?> methodClass;
		String methodName;
		if (methodString.contains(".")) {
			String[] splittedField = methodString.split("\\.");
			String className = splittedField[0].replaceAll("/", ".");
			try {
				methodClass = Class.forName(className);
			} catch (ClassNotFoundException e) {
				String message = "could not find class for name \"" + className + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
			}
			methodName = splittedField[1];
		} else {
			methodClass = this.componentClass;
			methodName = methodString;
		}

		/** get parameter types */
		List<Class<?>> parameterTypesList;
		if (matcher.group("parametertypes") != null && matcher.group("parametertypes") != "")
			parameterTypesList = this.getParameterTypes(matcher.group("parametertypes"));
		else
			parameterTypesList = new LinkedList<Class<?>>();

		AccessibleObject object;
		try {
			if (methodName.equals("\"<init>\""))
				object = methodClass.getDeclaredConstructor(parameterTypesList.toArray(new Class[parameterTypesList.size()]));
			else
				object = methodClass.getDeclaredMethod(methodName, parameterTypesList.toArray(new Class[parameterTypesList.size()]));
		} catch (NoSuchMethodException | SecurityException e) {
			StringBuilder parameterString = new StringBuilder();
			for (Class<?> cls : parameterTypesList) {
				if (parameterString.length() > 0)
					parameterString.append(", ");
				parameterString.append(cls.getCanonicalName());
			}

			String message;
			if (methodName.equals("\"<init>\""))
				message = "could not find constructor with parameters \"(" + parameterString.toString() + ")\" for class \"" + methodClass.getCanonicalName() + "\"";
			else
				message = "could not find method \"" + methodName + "(" + parameterString.toString() + ")\" for class \"" + methodClass.getCanonicalName() + "\"";
			Logger.getLogger(Disassembler.class).fatal(message);
			throw new DisassemblerException(message);
		}

		this.bytecodeLines.put(lineNumber, new BytecodeLineConstantTableAccessibleObject(
				line, lineNumber, Opcode.fromString(matcher.group("opcode")),
				Integer.parseInt(matcher.group("index")), object));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 * @param lines
	 * @param index
	 * 
	 * @return
	 */
	private int parseTableswitch(String line, String[] lines, int index) {
		Matcher matcher = tableswitchPattern.matcher(line);
		if (matcher.matches()) {
			int lineNumber = Integer.parseInt(matcher.group("number"));
	
			BytecodeLineTableswitch bytecodeLineTableSwitch = new BytecodeLineTableswitch(
					line, lineNumber, Opcode.fromString(matcher.group("opcode")));
	
			int i = index;
			while (i+1<lines.length && lines[i+1].matches(tableswitchCasePattern.pattern())) {
				++i;
	
				bytecodeLineTableSwitch.getOffsetsMap().put(
						lines[i].replaceAll(tableswitchCasePattern.pattern(), "${case}"),
						Integer.parseInt(lines[i].replaceAll(tableswitchCasePattern.pattern(), "${offset}")));
			}
	
			this.bytecodeLines.put(lineNumber, bytecodeLineTableSwitch);
	
			return i - index;
		} else
			return -1;
	}

	/**
	 * COMMENT
	 * 
	 * @param typeString
	 * 
	 * @return
	 */
	private List<Class<?>> getParameterTypes(String typeString) {
		List<Class<?>> parameters = new LinkedList<Class<?>>();

		StringBuilder currentType = new StringBuilder();
		boolean isPrimitivType = true;
		boolean isArrayType = false;
		for (char c : typeString.toCharArray()) {
			if (isPrimitivType && this.isPrimitivTypeCharacter(c) || !isPrimitivType && c == ';') {
				if (isPrimitivType || isArrayType)
					currentType.append(c);
				parameters.add(this.getClassForName(currentType.toString()));
				currentType = new StringBuilder();
				isPrimitivType = true;
				isArrayType = false;
			} else if (c == 'L') {
				if (isArrayType)
					currentType.append(c);
				isPrimitivType = false;
			} else if (!isPrimitivType && c == '/')
				currentType.append('.');
			else if (!isPrimitivType || c == '[') {
				if (c == '[')
					isArrayType = true;
				currentType.append(c);
			} else {
				String message = "unexpected character \"" + c + "\" in parameter type string \"" + typeString + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
			}
		}

		return parameters;
	}

	/**
	 * COMMENT
	 * 
	 * B byte
	 * C char
	 * D double
	 * F float
	 * I int
	 * J long
	 * S short
	 * Z boolean
	 * 
	 * @param c
	 * 
	 * @return
	 */
	private boolean isPrimitivTypeCharacter(char c) {
		return c == 'B' || c == 'C' || c == 'D' || c == 'F' || c == 'I' || c == 'J' || c == 'S' || c == 'Z';
	}

	/**
	 * COMMENT
	 * 
	 * @param className
	 * 
	 * @return
	 */
	private Class<?> getClassForName(String className) {
		if (className.equals("B"))
			return byte.class;
		else if(className.equals("C"))
			return char.class;
		else if(className.equals("D"))
			return double.class;
		else if(className.equals("F"))
			return float.class;
		else if(className.equals("I"))
			return int.class;
		else if(className.equals("J"))
			return long.class;
		else if(className.equals("S"))
			return short.class;
		else if(className.equals("Z"))
			return boolean.class;
		else {
			try {
				return Class.forName(className);
			} catch (ClassNotFoundException e) {
				String message = "could not find class for name \"" + className + "\"";
				Logger.getLogger(Disassembler.class).fatal(message);
				throw new DisassemblerException(message);
			}
		}
	}

	/** static methods
	 * ----- ----- ----- ----- */

	/**
	 * disassemble instantiates a new disassembler with the given method and
	 *  returns the disassembled method.
	 * 
	 * @param componentClass the class of the component for the method
	 * @param method COMMENT
	 * @param methodSignature the signature of the method
	 * @param disassembledMethod the disassembled method
	 * 
	 * @return the disassembled method object of the given method
	 */
	public static DisassembledMethod disassemble(Class<?> componentClass, Method method, String methodSignature, String disassembledMethod) {
		return new Disassembler(componentClass, method, methodSignature, disassembledMethod).disassemble();
	}

	/**
	 * COMMENT
	 * 
	 * @param method
	 * 
	 * @return
	 */
	public static DisassembledMethod disassemble(Method method) {
		/** disassemble class */
		String disassembledClass = getBytecode(method.getDeclaringClass());

		/** create method signature string */
		StringBuilder methodSignature = new StringBuilder();
		methodSignature.append(Modifier.toString(method.getModifiers()));
		methodSignature.append(" ");
		methodSignature.append(method.getReturnType().getCanonicalName());
		methodSignature.append(" ");
		methodSignature.append(method.getName());
		methodSignature.append("(");
		boolean firstParameterType = true;
		for (Class<?> cls : method.getParameterTypes()) {
			if (!firstParameterType)
				methodSignature.append(", ");
			else
				firstParameterType = false;

			methodSignature.append(cls.getCanonicalName());
		}
		methodSignature.append(");");

		/** split methods */
		for (String methodCode : disassembledClass.toString().split("\n\n")) {
			StringBuilder trimmedMethod = new StringBuilder();
			/** split lines of the method */
			boolean signatureLine = true;
			for (String methodCodeLine : methodCode.split("\n")) {
				if (methodCodeLine.trim().matches("^(class|public class|}|Code:|Compiled).*"))
					continue;

				/** check for method with right signature */
				if (signatureLine && !methodCodeLine.trim().equals(methodSignature.toString()))
					break;
				else if (signatureLine) {
					signatureLine = false;
					continue;
				}

				/** append line of bytecode */
				trimmedMethod.append(methodCodeLine.trim());
				trimmedMethod.append("\n");
			}

			if (!signatureLine) {
				return Disassembler.disassemble(
						method.getDeclaringClass(),
						method,
						methodSignature.toString(),
						trimmedMethod.toString());
			}
		}

		/** could never happen, because the method defines the class to
		 * disassemble */
		throw new RuntimeException("something went terribly wrong!");
	}

	/**
	 * COMMENT
	 *  
	 * @param componentClass
	 * 
	 * @return
	 */
	public static Map<String, DisassembledMethod> disassemble(Class<?> componentClass) {
		String disassembledClass = getBytecode(componentClass);

		List<Method> constraintMethods = RefactoringUtils.getConstraintMethods(componentClass);
		Map<String, DisassembledMethod> disassembledMethods = new HashMap<String, DisassembledMethod>();

		for (String methodCode : disassembledClass.toString().split("\n\n")) {
			String trimmedMethodSignature = "";
			StringBuilder trimmedMethod = new StringBuilder();
			for (String methodCodeLine : methodCode.split("\n")) {
				if (!(methodCodeLine.trim().matches("^(class|public class|}|Code:).*"))) {
					if (methodCodeLine.trim().matches("^(public |private )?boolean .*"))
						trimmedMethodSignature = methodCodeLine.trim().replaceAll(", ", ",");
					else {
						trimmedMethod.append(methodCodeLine.trim());
						trimmedMethod.append("\n");
					}
				}
			}

			boolean skip = true;
			Method method = null;
			for (Method m : constraintMethods) {
				if ((m.toGenericString().replaceAll(" \\S*\\.([^\\.]+)\\(", " $1(") + ";").replaceAll(", ", ",").equals(trimmedMethodSignature)) {
					method = m;
					skip = false;
					break;
				}
			}

			if (!skip && trimmedMethodSignature != "")
				disassembledMethods.put(trimmedMethodSignature, Disassembler.disassemble(componentClass, method, trimmedMethodSignature, trimmedMethod.toString()));
		}

		return disassembledMethods;
	}

	/** private static methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * getDisassembledClass returns class disassembled by javap.
	 * 
	 * @param componentClass the class to disassemble
	 * 
	 * @return the class disassembled by javap
	 */
	private static String getBytecode(Class<?> componentClass) {
		StringBuilder command = new StringBuilder("javap -classpath / -c -p ");
		if (componentClass.getProtectionDomain().getCodeSource() == null) {
			String message = "could not read class file for class \"" + componentClass.getSimpleName() + "\"";
			Logger.getLogger(RefactoringUtils.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		command.append(componentClass.getProtectionDomain().getCodeSource().getLocation().getPath());
		command.append(componentClass.getName().replaceAll("\\.", "/"));

		Process p = null;
		try {
			p = Runtime.getRuntime().exec(command.toString());
			return IOUtils.readFromStream(p.getInputStream());
		} catch (IOException e) {
			String message = "could not read class file for class \"" + componentClass.getSimpleName() + "\"";
			Logger.getLogger(RefactoringUtils.class).fatal(message);
			throw new IllegalArgumentException(message);
		} finally {
			if (p != null)
				p.destroy();
		}
	}
}
