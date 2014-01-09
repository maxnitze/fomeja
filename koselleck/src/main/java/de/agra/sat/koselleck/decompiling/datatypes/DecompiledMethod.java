package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * DecompiledMethod represents a a method decompiled by the decompiler.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class DecompiledMethod {
	/** constraint of the decompiled method ({@code true} if the return Value
	 * is set properly) */
	public final AbstractConstraint constraint;
	/** the return value of the method */
	public final AbstractConstraintValue returnValue;
	
	/**
	 * Constructor for a new decompiled method.
	 * 
	 * @param constraint the constraint of the decompiled method
	 * @param returnValue the return value of the decompiled method
	 */
	public DecompiledMethod(AbstractConstraint constraint, AbstractConstraintValue returnValue) {
		this.constraint = constraint;
		this.returnValue = returnValue;
	}
}
