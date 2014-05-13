package de.agra.sat.koselleck.decompiling;

/** imports */
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;

import org.junit.BeforeClass;
import org.junit.Test;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLine;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineOffset;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineSimple;
import de.agra.sat.koselleck.disassembling.bytecodetypes.BytecodeLineValue;
import de.agra.sat.koselleck.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class DecompilerSimpleCompareTest {

	/**  */
	private static Map<Integer, BytecodeLine> bytecodeLinesMap;
	/**  */
	private static DisassembledMethod disassembledMethod;

	@BeforeClass
	public static void setUpBeforeClass() {
		bytecodeLinesMap = new HashMap<Integer, BytecodeLine>();

		bytecodeLinesMap.put(
				5, new BytecodeLineValue("5: iconst_0", 5, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				6, new BytecodeLineOffset("6: goto 10", 6, Opcode._goto, 10));
		bytecodeLinesMap.put(
				9, new BytecodeLineValue("9: iconst_1", 9, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				10, new BytecodeLineSimple("10: ireturn", 10, Opcode._return));

		disassembledMethod = new DisassembledMethod(null, "", "", bytecodeLinesMap);
	}

	@Test
	public void testEquals() {
		AbstractConstraint abstractConstraint;

		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmpeq 9", 2, Opcode.if_Xcmpeq, 9));

		/** 1 == 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));

		/** 1 == 0 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_0", 1, Opcode.Xconst_, 0));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));

		/** 0 == 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_0", 0, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));
	}

	@Test
	public void testNotEquals() {
		AbstractConstraint abstractConstraint;

		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmpne 9", 2, Opcode.if_Xcmpne, 9));

		/** 1 != 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));

		/** 1 != 0 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_0", 1, Opcode.Xconst_, 0));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));

		/** 0 != 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_0", 0, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));
	}

	@Test
	public void testGreaterThan() {
		AbstractConstraint abstractConstraint;

		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmpgt 9", 2, Opcode.if_Xcmpgt, 9));

		/** 1 > 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));

		/** 1 > 0 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_0", 1, Opcode.Xconst_, 0));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));

		/** 0 > 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_0", 0, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));
	}

	@Test
	public void testGreaterEquals() {
		AbstractConstraint abstractConstraint;

		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmpge 9", 2, Opcode.if_Xcmpge, 9));

		/** 1 >= 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));

		/** 1 >= 0 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_0", 1, Opcode.Xconst_, 0));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));

		/** 0 >= 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_0", 0, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));
	}

	@Test
	public void testLowerThan() {
		AbstractConstraint abstractConstraint;

		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmplt 9", 2, Opcode.if_Xcmplt, 9));

		/** 1 < 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));

		/** 1 < 0 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_0", 1, Opcode.Xconst_, 0));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));

		/** 0 < 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_0", 0, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));
	}

	@Test
	public void testLowerEquals() {
		AbstractConstraint abstractConstraint;

		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmple 9", 2, Opcode.if_Xcmple, 9));

		/** 1 <= 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));

		/** 1 <= 0 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_0", 1, Opcode.Xconst_, 0));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(false)));

		/** 0 <= 1 */
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_0", 0, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));

		abstractConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]).evaluate();

		assertTrue(abstractConstraint.equals(new AbstractBooleanConstraint(true)));
	}
}
