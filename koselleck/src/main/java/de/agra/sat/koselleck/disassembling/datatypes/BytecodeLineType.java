package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.MissformattedBytecodeLineException;

/**
 * BytecodeLineType represents the type of a byte code line.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class BytecodeLineType {
	/** the full line */
	public final String fullLine;
	/** the string of the type */
	public final String typeText;
	/** the type */
	public final EBytecodeLineType type;
	/** the accessible object */
	public final AccessibleObject accessibleObject;
	/** the type of the accessible object */
	public final Class<?> accessibleObjectType;
	/** the class */
	public final Class<?> clazz;
	/** the value object */
	public final Object value;
	
	/**
	 * Constructor for a new byte code line type.
	 * 
	 * @param componentClass the class of the current component
	 * @param fullLine the full byte code line
	 * 
	 * @throws MissformattedBytecodeLineException if the byte code line does
	 *  not fit the expected format
	 */
	public BytecodeLineType(Class<?> componentClass, String fullLine) throws MissformattedBytecodeLineException {
		this.fullLine = fullLine.trim().replaceAll("\\s+", " ");
		
		if(!this.fullLine.matches(BytecodeLineRegexes.typeRegex)) {
			String message = "no type or value given in bytecode line \"" + fullLine + "\"";
			Logger.getLogger(BytecodeLineType.class).fatal(message);
			throw new MissformattedBytecodeLineException(message);
		}
		
		this.typeText = this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${type} ${value}");
		
		this.type = EBytecodeLineType.fromString(
				this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${type}"));
		
		String className = null;
		String methodName = null;
		String value = null;
		switch(this.type) {
		case CLASS:
			this.accessibleObject = null;
			this.accessibleObjectType = null;
			
			className = this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${value}").replaceAll("/", ".");
			try {
				this.clazz = Class.forName(className);
			} catch (ClassNotFoundException e) {
				String message = "could not get class for name \"" + className + "\"";
				Logger.getLogger(BytecodeLineType.class).fatal(message);
				throw new MissformattedBytecodeLineException(message);
			}
			
			this.value = null;
			
			break;
			
		case FIELD:
			String field = this.fullLine.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${value}");
			if(field.contains(".")) {
				String[] splittedField = field.split("\\.");
				className = splittedField[0].replaceAll("/", ".");
				try {
					this.accessibleObject = Class.forName(className).getDeclaredField(splittedField[1]);
				} catch (NoSuchFieldException | SecurityException | ClassNotFoundException e) {
					String message = "could not find field \"" + splittedField[1] + "\" for class \"" + componentClass.getName() + "\"";
					Logger.getLogger(BytecodeLineType.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}
			} else {
				try {
					this.accessibleObject = componentClass.getDeclaredField(field);
				} catch (NoSuchFieldException | SecurityException e) {
					String message = "could not find field \"" + field + "\" for class \"" + componentClass.getName() + "\"";
					Logger.getLogger(BytecodeLineType.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}
			}
			this.accessibleObjectType = getClassFromDisassembledString(this.fullLine);
			
			this.clazz = null;
			this.value = null;
			
			break;
			
		case METHOD:
			String[] splittedField = this.fullLine.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${value}").split("\\.");
			String[] paramTypes = this.fullLine.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${paramtypes}").split(";");
			
			List<Class<?>> paramTypesList = new ArrayList<Class<?>>();
			for(String paramType : paramTypes) {
				className = paramType.replaceAll("/", ".");
				if(className == null || className.equals(""))
					continue;
				else if(className.equals("D"))
					paramTypesList.add(double.class);
				else if(className.equals("F"))
					paramTypesList.add(float.class);
				else if(className.equals("I"))
					paramTypesList.add(int.class);
				else {
					try {
						className = className.substring(1);
						paramTypesList.add(Class.forName(className));
					} catch (ClassNotFoundException e) {
						String message = "could not get class for name \"" + className + "\"";
						Logger.getLogger(BytecodeLineType.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					}
				}
			}
			
			className = splittedField[0].replaceAll("/", ".");
			methodName = splittedField[1];
			try {
				if(methodName.equals("\"<init>\""))
					this.accessibleObject = Class.forName(className).getDeclaredConstructor(paramTypesList.toArray(new Class[] {}));
				else
					this.accessibleObject = Class.forName(className).getDeclaredMethod(methodName, paramTypesList.toArray(new Class[] {}));
			} catch (NoSuchMethodException | SecurityException | ClassNotFoundException e) {
				StringBuilder methodArguments = new StringBuilder();
				for(Class<?> cls : paramTypesList) {
					if(methodArguments.length() > 0)
						methodArguments.append(", ");
					methodArguments.append(cls.getName());
				}
				
				String message = "could not find method \"" + methodName + "(" + methodArguments.toString() + ")\" for class \"" + className + "\"";
				Logger.getLogger(BytecodeLineType.class).fatal(message);
				throw new MissformattedBytecodeLineException(message);
			}
			this.accessibleObjectType = null;
			
			this.clazz = null;
			this.value = null;
			
			break;
			
		case VALUE:
			this.accessibleObject = null;
			this.accessibleObjectType = null;
			
			className = this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${type}");
			value = this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${value}");
			if(className.equals("double")) {
				this.clazz = Double.class;
				this.value = Double.parseDouble(value);
			} else if(className.equals("float")) {
				this.clazz = Float.class;
				this.value = Float.parseFloat(value);
			} else {
				String message = "unknown class \"" + className + "\" in bytecode line type value";
				Logger.getLogger(BytecodeLineType.class).fatal(message);
				throw new MissformattedBytecodeLineException(message);
			}
			break;
			
		default:
			String message = "unknown bytecode line type in line \"" + fullLine + "\"";
			Logger.getLogger(BytecodeLineType.class).fatal(message);
			throw new MissformattedBytecodeLineException(message);
		}
	}
	
	/**
	 * toString returns a string representation of the byte code line type.
	 * 
	 * @return a string representation of this byte code line type
	 */
	@Override
	public String toString() {
		switch(this.type) {
		case FIELD:
			return this.type + " " + ((Field)this.accessibleObject).toGenericString();
		case METHOD:
			return this.type + " " + ((Method)this.accessibleObject).toGenericString();
		case CLASS:
			return this.type + " " + this.clazz.getCanonicalName();
		default:
			return null;
		}
	}
	
	/** private methods
	 * ----- ----- ----- ----- */
	
	/**
	 * getClassFromDisassembledString returns the class of the the field of the
	 *  given disassembled string.
	 * 
	 * @param disassembledString the disassembled string to get the class of
	 *  the field from
	 * 
	 * @return the class of the field of the given disassembled string
	 */
	private Class<?> getClassFromDisassembledString(String disassembledString) {
		String classString = disassembledString.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${rtype}");
		
		if(classString == null)
			return null;
		
		else if(classString.equals("D"))
			return Double.class;
		
		else if(classString.equals("F"))
			return Float.class;
		
		else if(classString.equals("I"))
			return Integer.class;
		
		else
			return null;
		}
}
