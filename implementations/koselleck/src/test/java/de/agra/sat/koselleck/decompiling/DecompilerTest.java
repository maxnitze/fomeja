package de.agra.sat.koselleck.decompiling;

/** imports */
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;

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
public class DecompilerTest {

	@Test
	public void booleanConstraintMethod() {
		/** constraint method with body 'return 1 == 1' */
		Map<Integer, BytecodeLine> bytecodeLinesMap = new HashMap<Integer, BytecodeLine>();
		bytecodeLinesMap.put(
				0, new BytecodeLineValue("0: iconst_1", 0, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				1, new BytecodeLineValue("1: iconst_1", 1, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				2, new BytecodeLineOffset("2: if_icmpne 9", 2, Opcode.if_Xcmpne, 9));
		bytecodeLinesMap.put(
				5, new BytecodeLineValue("5: iconst_1", 5, Opcode.Xconst_, 1));
		bytecodeLinesMap.put(
				6, new BytecodeLineOffset("6: goto 10", 6, Opcode._goto, 10));
		bytecodeLinesMap.put(
				9, new BytecodeLineValue("9: iconst_0", 9, Opcode.Xconst_, 0));
		bytecodeLinesMap.put(
				10, new BytecodeLineSimple("10: ireturn", 10, Opcode._return));

		DisassembledMethod disassembledMethod = new DisassembledMethod(null, "", "", bytecodeLinesMap);

		AbstractConstraint abstractTrueConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]);

		assertTrue(abstractTrueConstraint.evaluate().equals(new AbstractBooleanConstraint(true)));

		/** change body of constraint method to 'return 1 == 0' */
		bytecodeLinesMap.put(
				5, new BytecodeLineValue("5: iconst_0", 5, Opcode.Xconst_, 0));

		disassembledMethod = new DisassembledMethod(null, "", "", bytecodeLinesMap);

		AbstractConstraint abstractFalseConstraint = Decompiler.decompile(
				disassembledMethod,
				new AbstractConstraintLiteralObject(null),
				new AbstractConstraintValue[0]);

		assertTrue(abstractFalseConstraint.evaluate().equals(new AbstractBooleanConstraint(false)));
	}
}
