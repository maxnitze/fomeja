package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.LinkedList;
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
	/** COMMENT */
	private static final Pattern simpleTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.simpleTypeGroup + ")$");
	/** COMMENT */
	private static final Pattern valueTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.simpleValueTypeGroup + ")(?<value>[+-]?[0-9]+(\\.[0-9]+)?)$");
	/** COMMENT */
	private static final Pattern constantTableValueTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.constantTableValueTypeGroup + ") #\\d+ // (float|double) (?<value>[+-]?[0-9]+(\\.[0-9]+)?)(?<valuetype>[f|d])$");
	/** COMMENT */
	private static final Pattern offsetTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.offsetTypeGroup + ") (?<offset>\\d+)$");
	/** COMMENT */
	private static final Pattern constantTableAccessibleObjectTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.constantTableIndexTypeGroup + ") #(?<index>\\d+) // (?<accessibleobjecttype>Field|Method) (?<accessibleobject>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$");
	/** COMMENT */
	private static final Pattern constantTableClassTypePattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.constantTableIndexTypeGroup + ") #(?<index>\\d+) // class (?<class>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$");
	/** COMMENT */
	private static final Pattern tableswitchPattern =
			Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.switchTypeGroup + ") \\{ // \\d+ to \\d+$");
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
			/** is value bytecode line */
			else if (disassembledMethodLine.matches(valueTypePattern.pattern()))
				this.parseValueType(disassembledMethodLine);
			/** is offset bytecode line */
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
				throw new MissformattedBytecodeLineException(message);
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
		matcher.find();

		int lineNumber = Integer.parseInt(matcher.group("number"));

		this.bytecodeLines.put(lineNumber, new BytecodeLineSimple(
				line, lineNumber, Opcode.fromString(matcher.group("opcode"))));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseValueType(String line) {
		Matcher matcher = valueTypePattern.matcher(line);
		matcher.find();

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
		} else
			value = valueString;

		this.bytecodeLines.put(lineNumber, new BytecodeLineValue(
				line, lineNumber, Opcode.fromString(opcodeString), value));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseConstantTableValueType(String line) {
		Matcher matcher = constantTableValueTypePattern.matcher(line);
		matcher.find();

		int lineNumber = Integer.parseInt(matcher.group("number"));
		String valueTypeString = matcher.group("valuetype");

		Object value;
		if (valueTypeString.equals("f"))
			value = Float.parseFloat(matcher.group("value"));
		else if (valueTypeString.equals("d"))
			value = Double.parseDouble(matcher.group("value"));
		else
			value = matcher.group("value");

		this.bytecodeLines.put(lineNumber, new BytecodeLineValue(
				line, lineNumber, Opcode.fromString(matcher.group("opcode")), value));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseOffsetType(String line) {
		Matcher matcher = offsetTypePattern.matcher(line);
		matcher.find();

		int lineNumber = Integer.parseInt(matcher.group("number"));

		this.bytecodeLines.put(lineNumber, new BytecodeLineOffset(
				line, lineNumber, Opcode.fromString(matcher.group("opcode")),
				Integer.parseInt(matcher.group("offset"))));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseConstantTableClassType(String line) {
		Matcher matcher = constantTableClassTypePattern.matcher(line);
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

		this.bytecodeLines.put(lineNumber, new BytecodeLineConstantTableClass(
				line, lineNumber, Opcode.fromString(matcher.group("opcode")),
				Integer.parseInt(matcher.group("index")), clazz));
	}

	/**
	 * COMMENT
	 * 
	 * @param line
	 */
	private void parseConstantTableAccessibleObjectType(String line) {
		Matcher matcher = constantTableAccessibleObjectTypePattern.matcher(line);
		matcher.find();

		int lineNumber = Integer.parseInt(matcher.group("number"));

		String accessibleObjectType = matcher.group("accessibleobjecttype");

		/** accessible object is a field */
		if (accessibleObjectType.equals("Field"))
			this.parseConstantTableAccessibleObjectTypeField(line, matcher, lineNumber);
		/** accessible object is a method */
		else if (accessibleObjectType.equals("Method"))
			this.parseConstantTableAccessibleObjectTypeMethod(line, matcher, lineNumber);
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
				throw new MissformattedBytecodeLineException(message);
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
			throw new MissformattedBytecodeLineException(message);
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
		matcher.find();

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
				throw new MissformattedBytecodeLineException(message);
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
				throw new MissformattedBytecodeLineException(message);
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
