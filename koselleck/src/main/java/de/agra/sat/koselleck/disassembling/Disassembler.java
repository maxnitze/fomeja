package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * Disassembler implements a disassembler for java byte code.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Disassembler {
	public static final String simpleTypeRegex = "^(?<number>\\d+): (?<opcode>" + Opcode.getSimpleTypeGroup() + ")$";
	public static final String simpleValueTypeRegex = "^(?<number>\\d+): (?<opcode>" + Opcode.getValueTypeGroup() + ")_(?<value>\\d+)$";
	public static final String valueTypeRegex = "^(?<number>\\d+): (?<opcode>" + Opcode.getValueTypeGroup() + ") (?<value>\\d+)$";
	public static final String offsetTypeRegex = "^(?<number>\\d+): (?<opcode>" + Opcode.getOffsetTypeGroup() + ") (?<offset>\\d+)$";
	
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
		
		Map<Integer, BytecodeLine> bytecodeLines = new HashMap<Integer, BytecodeLine>();
		
		String[] methodLines = this.disassembledMethodString.split("\n");
		for(int i=0; i<methodLines.length; i++) {
			
//			BytecodeLine bytecodeLine = new BytecodeLine(this.componentClass, methodLines[i]);
//			bytecodeLines.put(bytecodeLine.lineNumber, bytecodeLine);
//			if(bytecodeLine.opcode == Opcode.tableswitch)
//				while(methodLines[i+1].matches(BytecodeLineRegexes.switchCase))
//					bytecodeLine.switchOffsets.put(
//							methodLines[++i].replaceAll(BytecodeLineRegexes.switchCase, "${case}"),
//							Integer.parseInt(methodLines[i].replaceAll(BytecodeLineRegexes.switchCase, "${offset}")));
			
			this.componentClass.getName();
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
