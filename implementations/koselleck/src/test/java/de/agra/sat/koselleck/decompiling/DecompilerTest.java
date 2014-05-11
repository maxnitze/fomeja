package de.agra.sat.koselleck.decompiling;

/** imports */
import static org.junit.Assert.assertFalse;

import java.util.HashSet;
import java.util.Map;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralClass;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.sat.koselleck.types.Opcode;
import de.agra.sat.koselleck.util.VariableInteger;
import de.agra.sat.koselleck.util.VariableIntegers;
import de.agra.sat.koselleck.utils.KoselleckUtils;

/**
 * 
 * @author Max Nitze
 */
public class DecompilerTest {
	/**  */
	private static Map<String, DisassembledMethod> disassembledMethodsMap;

	@BeforeClass
	public static void SetUpBeforeClass() {
		disassembledMethodsMap = KoselleckUtils.getDisassembledConstraintMethods(VariableIntegers.class);
	}

	/**
	 * 
	 * @throws Exception
	 */
	@Before
	public void setUp() throws Exception {
	}

	/**
	 * 
	 * @throws Exception
	 */
	@After
	public void tearDown() throws Exception {
	}

	/**
	 * 
	 */
	@Test
	public void testDecompile() {
		AbstractConstraint abstractConstraint = Decompiler.decompile(
				disassembledMethodsMap.get("public boolean variableIntegersDiffer(de.agra.sat.koselleck.util.VariableInteger,de.agra.sat.koselleck.util.VariableInteger);"),
				new AbstractConstraintLiteralObject(new VariableIntegers(new HashSet<VariableInteger>())),
				new AbstractConstraintLiteralClass[] {
					new AbstractConstraintLiteralClass(VariableInteger.class, Opcode.Xload, 1),
					new AbstractConstraintLiteralClass(VariableInteger.class, Opcode.Xload, 2) });

		assertFalse(abstractConstraint.equals(new AbstractBooleanConstraint(true)));
	}
}
