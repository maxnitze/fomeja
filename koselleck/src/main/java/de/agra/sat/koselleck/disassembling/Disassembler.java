package de.agra.sat.koselleck.disassembling;

/** imports */
import java.lang.reflect.Method;
import java.util.Map;
import java.util.TreeMap;

import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.datatypes.BytecodeLineRegexes;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class Disassembler {
	/**  */
	private final Object component;
	/**  */
	private final Method method;
	/**  */
	private final String methodSignature;
	/**  */
	private final String disassembledMethod;
	
	/**
	 * 
	 * @param component
	 * @param method
	 * @param methodSignature
	 * @param disassembledMethod
	 */
	private Disassembler(Object component, Method method, String methodSignature, String disassembledMethod) {
		this.component = component;
		this.method = method;
		this.methodSignature = methodSignature;
		this.disassembledMethod = disassembledMethod;
	}
	
	/**
	 * 
	 * @return
	 */
	private DisassembledMethod disassemble() {
		Map<Integer, BytecodeLine> bytecodeLines = new TreeMap<Integer, BytecodeLine>();
		BytecodeLine bytecodeLine = null;
		String[] methodLines = disassembledMethod.split("\n");
		for(int i=0; i<methodLines.length; i++) {
			bytecodeLine = new BytecodeLine(this.component, methodLines[i]);
			bytecodeLines.put(bytecodeLine.lineNumber, bytecodeLine);
			if(bytecodeLine.opcode == Opcode.tableswitch) {
				while(methodLines[i+1].matches(BytecodeLineRegexes.switchCase)) {
					System.out.println("- " + methodLines[i+1]);
					bytecodeLine.switchOffsets.put(
							methodLines[++i].replaceAll(BytecodeLineRegexes.switchCase, "${case}"),
							Integer.parseInt(methodLines[i].replaceAll(BytecodeLineRegexes.switchCase, "${offset}")));
				}
			}
		}
		
		return new DisassembledMethod(this.method, this.methodSignature, this.disassembledMethod, bytecodeLines);
	}
	
	/**
	 * 
	 * @param component
	 * @param methodSignature
	 * @param disassembledMethod
	 * 
	 * @return
	 */
	public static DisassembledMethod disassemble(Object component, Method method, String methodSignature, String disassembledMethod) {
		Disassembler disassembler = new Disassembler(component, method, methodSignature, disassembledMethod);
		return disassembler.disassemble();
	}
}
