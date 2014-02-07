package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine.BytecodeLineType;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineSimple;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineValue;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * Disassembler implements a disassembler for java byte code.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Disassembler {
	private final Pattern simpleTypePattern = Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleTypeGroup() + ")$");
	private final Pattern simpleValueTypePattern = Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getValueTypeGroup() + ")_(?<value>\\d+)$");
	private final Pattern valueTypePattern = Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getValueTypeGroup() + ") (?<value>\\d+)$");
	private final Pattern offsetTypePattern = Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$");
	private final Pattern constantTableIndexTypePattern = Pattern.compile("^(?<number>\\d+): (?<opcode>" + Opcode.getConstantTableIndexTypeGroup() + ") (?<offset>\\d+)$");
	
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
		
		/** match simple type */
		Matcher simpleTypeMatcher = this.simpleTypePattern.matcher(this.disassembledMethodString);
		while(simpleTypeMatcher.find()) {
			int lineNumber = Integer.parseInt(simpleTypeMatcher.group("number"));
			bytecodeLines.put(lineNumber, new BytecodeLineSimple(
					simpleTypeMatcher.group(), lineNumber, Opcode.fromString(simpleTypeMatcher.group("opcode")), lineNumber + 1, BytecodeLineType.SIMPLE));
		}
		
		/** match simple value type */
		Matcher simpleValueTypeMatcher = this.simpleValueTypePattern.matcher(this.disassembledMethodString);
		while(simpleValueTypeMatcher.find()) {
			int lineNumber = Integer.parseInt(simpleValueTypeMatcher.group("number"));
			
			bytecodeLines.put(lineNumber, new BytecodeLineValue(
					simpleTypeMatcher.group(), lineNumber, Opcode.fromString(simpleTypeMatcher.group("opcode")), lineNumber + 1, BytecodeLineType.SIMPLE));
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
