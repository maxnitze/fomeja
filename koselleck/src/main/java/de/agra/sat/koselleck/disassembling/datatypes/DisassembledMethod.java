package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.lang.reflect.Method;
import java.util.Map;

/**
 * 
 * @author Max Nitze
 */
public class DisassembledMethod {
	/**  */
	public final Method method;
	
	/**  */
	public final String methodSignature;
	/**  */
	public final String disassembledMethod;
	
	/**  */
	public final Map<Integer, BytecodeLine> bytecodeLines;
	
	/**
	 * 
	 * @param method
	 * @param methodSignature
	 * @param disassembledMethod
	 * @param bytecodeLines
	 */
	public DisassembledMethod(Method method, String methodSignature, String disassembledMethod, Map<Integer, BytecodeLine> bytecodeLines) {
		this.method = method;
		
		this.methodSignature = methodSignature;
		this.disassembledMethod = disassembledMethod;
		
		this.bytecodeLines = bytecodeLines;
		
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		return this.methodSignature + "\n" + disassembledMethod;
	}
}
