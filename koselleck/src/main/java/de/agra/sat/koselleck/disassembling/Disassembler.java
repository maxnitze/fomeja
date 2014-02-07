package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

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
	private final String simpleTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleTypeGroup() + ")$";
	/**  */
	private final String simpleValueTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleValueTypeGroup() + ")_(?<value>\\d+)$";
	/**  */
	private final String valueTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getValueTypeGroup() + ") (?<value>\\d+)$";
	/**  */
	private final String constantTableValueTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableValueTypeGroup() + ") #\\d+ // (float|double) (?<value>\\d+)(?<valuetype>[f|d])$";
	/**  */
	private final String offsetTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$";
	/**  */
	private final String constantTableAccessibleObjectTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) // (?<accessibleobjecttype>Field|Method) (?<accessibleobject>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$";
	/**  */
	private final String constantTableClassTypePattern = "^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") #(?<index>\\d+) // class (?<class>\\S+):(\\((?<parametertypes>\\S+)\\))?(?<returntype>\\S+)$"; // TODO might not be right
	
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
			if(disassembledMethodLine.matches(this.simpleTypePattern)) {
				int lineNumber = Integer.parseInt(disassembledMethodLine.replaceAll(this.simpleTypePattern, "$number"));
				
				bytecodeLines.put(lineNumber, new BytecodeLineSimple(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(disassembledMethodLine.replaceAll(this.simpleTypePattern, "$opcode"))));
			}
			/** is value bytecode line */
			else if(disassembledMethodLine.matches(this.simpleValueTypePattern) || disassembledMethodLine.matches(this.valueTypePattern)) {
				int lineNumber = Integer.parseInt(disassembledMethodLine.replaceAll(this.valueTypePattern, "$number"));
				String opcodeString = disassembledMethodLine.replaceAll(this.valueTypePattern, "$opcode");
				String valueString = disassembledMethodLine.replaceAll(this.valueTypePattern, "$value");
				
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
			else if(disassembledMethodLine.matches(this.constantTableValueTypePattern)) {
				int lineNumber = Integer.parseInt(disassembledMethodLine.replaceAll(this.constantTableValueTypePattern, "$number"));
				String valueTypeString = disassembledMethodLine.replaceAll(this.constantTableValueTypePattern, "$valuetype");
				
				Object value;
				if(valueTypeString.equals("f"))
					value = Float.parseFloat(disassembledMethodLine.replaceAll(this.constantTableValueTypePattern, "$value"));
				else if(valueTypeString.equals("d"))
					value = Double.parseDouble(disassembledMethodLine.replaceAll(this.constantTableValueTypePattern, "$value"));
				else
					value = disassembledMethodLine.replaceAll(this.constantTableValueTypePattern, "$value");
				
				bytecodeLines.put(lineNumber, new BytecodeLineValue(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(disassembledMethodLine.replaceAll(this.constantTableValueTypePattern, "$opcode")), value));
			}
			/** is offset bytecode line */
			else if(disassembledMethodLine.matches(this.offsetTypePattern)) {
				int lineNumber = Integer.parseInt(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$number"));
				
				bytecodeLines.put(lineNumber, new BytecodeLineOffset(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$opcode")),
						Integer.parseInt(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$offset"))));
			}
			/** is constant table class bytecode line */
			else if(disassembledMethodLine.matches(this.constantTableClassTypePattern)) {
				int lineNumber = Integer.parseInt(disassembledMethodLine.replaceAll(this.constantTableClassTypePattern, "$number"));
				
				String accessibleObjectType = disassembledMethodLine.replaceAll(this.constantTableClassTypePattern, "$class");
				Class<?> clazz;
				try {
					clazz = Class.forName(disassembledMethodLine.replaceAll(this.constantTableClassTypePattern, "$class"));
				} catch (ClassNotFoundException e) {
					String message = "";
					Logger.getLogger(Disassembler.class).fatal(message);
					throw new MissformattedBytecodeLineException(message);
				}
				
				bytecodeLines.put(lineNumber, new BytecodeLineConstantTableClass(
						disassembledMethodLine, lineNumber,
						Opcode.fromString(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$opcode")),
						Integer.parseInt(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$index")), clazz));
			}
			/** is constant table accessible object bytecode line */
			else if(disassembledMethodLine.matches(this.constantTableAccessibleObjectTypePattern)) {
				int lineNumber = Integer.parseInt(disassembledMethodLine.replaceAll(this.constantTableAccessibleObjectTypePattern, "$number"));
				
				String accessibleObjectType = disassembledMethodLine.replaceAll(this.constantTableAccessibleObjectTypePattern, "$accessibleobjecttype");
				/**  */
				if(accessibleObjectType.equals("Field")) {
					Class<?> clazz;
					try {
						clazz = Class.forName(disassembledMethodLine.replaceAll(this.constantTableAccessibleObjectTypePattern, "$accessibleobjecttype"));
					} catch (ClassNotFoundException e) {
						String message = "";
						Logger.getLogger(Disassembler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					}
					bytecodeLines.put(lineNumber, new BytecodeLineConstantTableAccessibleObject(
							disassembledMethodLine, lineNumber,
							Opcode.fromString(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$opcode")),
							Integer.parseInt(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$index")), clazz));
				}
				/**  */
				else if(accessibleObjectType.equals("Field")) {
					Class<?> clazz;
					try {
						clazz = Class.forName(disassembledMethodLine.replaceAll(this.constantTableAccessibleObjectTypePattern, "$accessibleobjecttype"));
					} catch (ClassNotFoundException e) {
						String message = "";
						Logger.getLogger(Disassembler.class).fatal(message);
						throw new MissformattedBytecodeLineException(message);
					}
					bytecodeLines.put(lineNumber, new BytecodeLineConstantTableAccessibleObject(
							disassembledMethodLine, lineNumber,
							Opcode.fromString(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$opcode")),
							Integer.parseInt(disassembledMethodLine.replaceAll(this.offsetTypePattern, "$index")), clazz));
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
