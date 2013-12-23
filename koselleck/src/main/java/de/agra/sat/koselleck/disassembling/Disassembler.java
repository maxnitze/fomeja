package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineRegexes;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * Disassembler implements a disassembler for java byte code.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Disassembler {
	/** the component */
	private final Object component;
	/** the method to disassemble */
	private final Method method;
	/** the signature of the method */
	private final String methodSignature;
	/** the java byte code of the method */
	private final String disassembledMethod;
	
	/**
	 * Constructor for a new disassembler.
	 * 
	 * @param component the new component
	 * @param method the new method
	 * @param methodSignature the new method signature
	 * @param disassembledMethod the new java byte code of the method
	 */
	private Disassembler(Object component, Method method, String methodSignature, String disassembledMethod) {
		this.component = component;
		this.method = method;
		this.methodSignature = methodSignature;
		this.disassembledMethod = disassembledMethod;
	}
	
	/**
	 * disassemble splits the disassembled method into its lines and returns a
	 *  disassembled method with a map of the single byte code lines.
	 * 
	 * @return a disassembled method with a map of the single byte code lines
	 */
	private DisassembledMethod disassemble() {
		Map<Integer, BytecodeLine> bytecodeLines = new HashMap<Integer, BytecodeLine>();
		String[] methodLines = disassembledMethod.split("\n");
		for(int i=0; i<methodLines.length; i++) {
			BytecodeLine bytecodeLine = new BytecodeLine(this.component, methodLines[i]);
			bytecodeLines.put(bytecodeLine.lineNumber, bytecodeLine);
			if(bytecodeLine.opcode == Opcode.tableswitch)
				while(methodLines[i+1].matches(BytecodeLineRegexes.switchCase))
					bytecodeLine.switchOffsets.put(
							methodLines[++i].replaceAll(BytecodeLineRegexes.switchCase, "${case}"),
							Integer.parseInt(methodLines[i].replaceAll(BytecodeLineRegexes.switchCase, "${offset}")));
		}
		
		return new DisassembledMethod(this.method, this.methodSignature, this.disassembledMethod, bytecodeLines);
	}
	
	/** static methods
	 * ----- ----- ----- ----- */
	
	/**
	 * disassemble instantiates a new disassembler with the given method and
	 *  returns the disassembled method.
	 * 
	 * @param component the component for the method
	 * @param methodSignature the signature of the method
	 * @param disassembledMethod the disassembled method
	 * 
	 * @return the disassembled method object of the given method
	 */
	public static DisassembledMethod disassemble(Object component, Method method, String methodSignature, String disassembledMethod) {
		
		System.out.println(disassembledMethod); // TODO delete
		
		Disassembler disassembler = new Disassembler(component, method, methodSignature, disassembledMethod);
		return disassembler.disassemble();
	}
}
