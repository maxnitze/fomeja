package de.agra.sat.koselleck.disassembling.datatypes;

/** imports */
import java.lang.reflect.Method;
import java.util.Map;

/**
 * DisassembledMethod represents a disassembled method.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class DisassembledMethod {
	/** the method to disassemble */
	public final Method method;
	
	/** the signature of the method */
	public final String methodSignature;
	/** the disassembled method */
	public final String disassembledMethod;
	
	/** a map of all lines of the disassembled method */
	public final Map<Integer, BytecodeLine> bytecodeLines;
	
	/**
	 * Constructor for a new disassembled method.
	 * 
	 * @param method the new method
	 * @param methodSignature the new signature of the method
	 * @param disassembledMethod the new disassembled method
	 * @param bytecodeLines the new map of all lines of the disassembled method
	 */
	public DisassembledMethod(Method method, String methodSignature, String disassembledMethod, Map<Integer, BytecodeLine> bytecodeLines) {
		this.method = method;
		
		this.methodSignature = methodSignature;
		this.disassembledMethod = disassembledMethod;
		
		this.bytecodeLines = bytecodeLines;
		
	}
	
	/**
	 * toString returns the string representation of the disassembled method.
	 * 
	 * @return the string representation of the disassembled method
	 */
	@Override
	public String toString() {
		return this.methodSignature + "\n" + disassembledMethod;
	}
}
