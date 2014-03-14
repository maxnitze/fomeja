package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

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
		
		if(!this.fullLine.matches(BytecodeLineRegexes.typeRegex))
			throw new MissformattedBytecodeLineException("no type and/or class/method/field given");
		
		this.typeText = this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${type} ${qfield}");
		
		this.type = EBytecodeLineType.fromString(this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${type}"));
		
		if(this.type == EBytecodeLineType.FIELD) {
			String field = this.fullLine.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${qfield}");
			if(field.contains(".")) {
				String[] splittedField = field.split("\\.");
				try {
					this.accessibleObject = Class.forName(splittedField[0].replaceAll("/", ".")).getDeclaredField(splittedField[1]);
				} catch (NoSuchFieldException | SecurityException | ClassNotFoundException e) {
					throw new MissformattedBytecodeLineException("field of unknown class or field not found: " + e.getMessage());
				}
			} else {
				try {
					this.accessibleObject = componentClass.getDeclaredField(field);
				} catch (NoSuchFieldException | SecurityException e) {
					throw new MissformattedBytecodeLineException("field not found: " + e.getMessage());
				}
			}
			this.accessibleObjectType = getClassFromDisassembledString(this.fullLine);
			
			this.clazz = null;
		} else if(this.type == EBytecodeLineType.METHOD) {
			String[] splittedField = this.fullLine.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${qfield}").split("\\.");
			String[] paramTypes = this.fullLine.replaceAll(BytecodeLineRegexes.typeMethodFieldRegex, "${paramtypes}").split(";");
			
			List<Class<?>> paramTypesList = new ArrayList<Class<?>>();
			for(String paramType : paramTypes) {
				String className = paramType.replaceAll("/", ".");
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
						throw new MissformattedBytecodeLineException("could not find class for name \"" + className + "\"");
					}
				}
			}
			
			try {
				this.accessibleObject = Class.forName(splittedField[0].replaceAll("/", ".")).getDeclaredMethod(splittedField[1], paramTypesList.toArray(new Class[] {}));
			} catch (NoSuchMethodException | SecurityException | ClassNotFoundException e) {
				throw new MissformattedBytecodeLineException("method of unknown class or method not found: " + e.getMessage() + " (" + e.getClass().getSimpleName() + ")");
			}
			this.accessibleObjectType = null;
			
			this.clazz = null;
		} else if(this.type == EBytecodeLineType.CLASS) {
			this.accessibleObject = null;
			this.accessibleObjectType = null;
			
			try {
				this.clazz = Class.forName(this.fullLine.replaceAll(BytecodeLineRegexes.typeRegex, "${qfield}").replaceAll("/", "."));
			} catch (ClassNotFoundException e) {
				throw new MissformattedBytecodeLineException("unknown class: " + e.getMessage());
			}
		} else
			throw new MissformattedBytecodeLineException("");
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
