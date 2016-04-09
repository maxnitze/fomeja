package de.uni_bremen.agra.fomeja.decompiling;

/* imports */
import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.annotations.PreparableMethod;
import de.uni_bremen.agra.fomeja.annotations.Variable;
import de.uni_bremen.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomClassExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.misc.StoreExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArrayelementExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArraylengthExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremConstructorExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremFieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremGetfieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremStmtSeqExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr.Keyword;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.decompiling.statements.AssignmentStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.BreakStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.IfThenElseStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.LoopStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.ReturnStmt;
import de.uni_bremen.agra.fomeja.decompiling.statements.StatementSeq;
import de.uni_bremen.agra.fomeja.disassembling.Disassembler;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLine;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineConstantTableAccessibleObject;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineConstantTableClass;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineMultipleValue;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineOffset;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineSimple;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineSimpleValue;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.BytecodeLineTableswitch;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.DisassembledMethod;
import de.uni_bremen.agra.fomeja.exceptions.DecompilerException;
import de.uni_bremen.agra.fomeja.exceptions.DisassemblerException;
import de.uni_bremen.agra.fomeja.types.ArithmeticOperator;
import de.uni_bremen.agra.fomeja.types.CompareOperator;
import de.uni_bremen.agra.fomeja.types.Opcode;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;
import de.uni_bremen.agra.fomeja.utils.ExpressionUtils;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class Decompiler {
	/** COMMENT */
	private static final Method intValueFloat = RefactoringUtils.getMethodForClass(Float.class, "intValue");
	/** COMMENT */
	private static final Method intValueDouble = RefactoringUtils.getMethodForClass(Double.class, "intValue");
	/** COMMENT */
	private static int overallDepth = -1;

	/** stack to process on */
	private final Stack<Expression> stack;
	/** store to store values */
	private final Map<Integer, StoreExpr> store;
	/** COMMENT */
	private int depth;

	/**
	 * Private constructor for a new Decompiler.
	 */
	public Decompiler() {
		this.stack = new Stack<Expression>();
		this.store = new HashMap<Integer, StoreExpr>();
		this.depth = -1;
	}

	/**
	 * decompile clears the stack and store and then returns the abstract
	 *  constraint starting at index zero of the byte code lines.
	 * 
	 * @param bytecodeLines the byte code lines of the method to decompile
	 * @param depth COMMENT
	 * @param invokationValue COMMENT
	 * @param argumentValues the method parameters
	 * 
	 * @return the expression starting at index 0 of the byte code lines
	 */
	public final StatementSeq decompile(Map<Integer, BytecodeLine> bytecodeLines, int depth, Expression invokationValue, Expression... argumentValues) {
		this.stack.clear();
		this.store.clear();

		this.depth = depth;
		if (this.depth <= overallDepth)
			this.depth = ++overallDepth;
		else
			overallDepth = this.depth;

		StatementSeq stmtSeq = new StatementSeq(this.depth);

		stmtSeq.addParam(new AssignmentStmt("store" + this.depth + "_0", invokationValue));
		this.store.put(0, new StoreExpr("store" + this.depth + "_0", invokationValue.getResultType()));

		for (int i=0; i<argumentValues.length; i++) {
			stmtSeq.addParam(new AssignmentStmt("store" + this.depth + "_" + (i+1), argumentValues[i]));
			this.store.put(i+1, new StoreExpr("store" + this.depth + "_" + (i+1), argumentValues[i].getResultType()));
		}

		stmtSeq.add(this.parseBytecode(bytecodeLines, 0, new RecursionList()));

		return stmtSeq;
	}

	/** parsing
	 * ----- ----- ----- ----- ----- */

	/**
	 * parseBytecode returns the constraint starting at the given index of the
	 *  map of byte code lines. Recursively every single constraint is added to
	 *  the abstract constraint.
	 * 
	 * @param bytecodeLines the byte code lines to process
	 * @param offset the offset of the byte code line to start from
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private StatementSeq parseBytecode(Map<Integer, BytecodeLine> bytecodeLines, int offset, RecursionList recList) {
		BytecodeLine bytecodeLine;
		int nextOffset = offset;

		StatementSeq stmtSeq = new StatementSeq(this.depth);

		int index;
		Object value;

		Expression stackExpr;
		StoreExpr storeExpr;

		do {
			bytecodeLine = bytecodeLines.get(nextOffset);
			if (bytecodeLine == null) {
				String message = "tried to parse unavailable bytecode line at line \"" + nextOffset + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
			nextOffset = bytecodeLine.getFollowingLineNumber();

			/* remove skipped recursion elements from the recursion list */
			if (recList.skipsCurrentRecursion(offset)) {
				recList.remove();
				stmtSeq.add(new BreakStmt());
				return stmtSeq;
			}

			switch(bytecodeLine.getOpcode()) {
			case Xload_:
			case Xload:
				this.stack.push(this.store.get(((BytecodeLineSimpleValue) bytecodeLine).getValue()));
				break;

			case Xstore_:
			case Xstore:
				stackExpr = this.stack.pop();
				index = (Integer) ((BytecodeLineSimpleValue) bytecodeLine).getValue();

				stmtSeq.add(new AssignmentStmt("store" + this.depth + "_" + index, stackExpr));
				this.store.put(index, new StoreExpr("store" + this.depth + "_" + index, stackExpr.getResultType()));

				break;

			case iinc:
				index = (Integer) ((BytecodeLineMultipleValue) bytecodeLine).getValues()[0];
				storeExpr = this.store.get(index);
				Expression calculatedValue = this.getCalculatedValue(
						storeExpr, ArithmeticOperator.ADD,
						new AtomIntegerExpr((Integer) ((BytecodeLineMultipleValue) bytecodeLine).getValues()[1]));

				stmtSeq.add(new AssignmentStmt(storeExpr.getName(), calculatedValue));

				break;

			case Xconst:
			case Xconst_:
			case bipush:
			case sipush:
				value = ((BytecodeLineSimpleValue) bytecodeLine).getValue();
				if (value instanceof Double)
					this.stack.push(new AtomDoubleExpr((Double) value));
				else if (value instanceof Float)
					this.stack.push(new AtomFloatExpr((Float) value));
				else if (value instanceof Integer)
					this.stack.push(new AtomIntegerExpr((Integer) value));
				else {
					String message = "can not push constant \"" + value + "\" of type \"" + value.getClass().getSimpleName() + "\" onto the stack";
					Logger.getLogger(Decompiler.class).fatal(message);
					throw new DecompilerException(message);
				}
				break;

			case getfield:
				this.parseBytecodeGetfield((BytecodeLineConstantTableAccessibleObject) bytecodeLine, recList);
				break;
			case getstatic:
				this.stack.push(this.getStaticFieldValue((BytecodeLineConstantTableAccessibleObject) bytecodeLine, recList));
				break;

			case checkcast:
				this.parseOpcodeCheckcast((BytecodeLineConstantTableClass) bytecodeLine);
				break;

			case i2f:
			case i2d:
			case f2d:
				this.parseOpcodeX2X(bytecodeLine.getOpcode());
				break;

			case irem:
			case frem:
			case drem:
			case lrem:
				this.parseOpcodeXrem(bytecodeLine.getOpcode());
				break;

			case ldc:
			case ldc2_w:
				this.parseOpcodeLdcX((BytecodeLineSimpleValue) bytecodeLine);
				break;

			case Xadd:
			case Xsub:
			case Xmul:
			case Xdiv:
				this.parseOpcodeXArithmetic((BytecodeLineSimple) bytecodeLine);
				break;

			case _new:
				this.stack.push(new AtomClassExpr(((BytecodeLineConstantTableClass) bytecodeLine).getType()));
				break;

			case invokestatic:
			case invokevirtual:
			case invokespecial:
				this.parseOpcodeInvokeX((BytecodeLineConstantTableAccessibleObject) bytecodeLine);
				break;

			case tableswitch:
				stmtSeq.add(this.parseOpcodeTableSwitch((BytecodeLineTableswitch) bytecodeLine, bytecodeLines, recList));
				return stmtSeq;

			case dup:
				this.stack.push(this.stack.peek());
				break;

			case newarray:
				this.parseOpcodeXNewarray((Class<?>) ((BytecodeLineSimpleValue) bytecodeLine).getValue());
				break;
			case anewarray:
				this.parseOpcodeXNewarray(((BytecodeLineConstantTableClass) bytecodeLine).getType());
				break;
			case arraylength:
				this.parseOpcodeArraylength();
				break;
			case Xaload:
				this.parseOpcodeXaload();
				break;
			case Xastore:
				this.parseOpcodeXastore();
				break;

			case _goto:
				stmtSeq.add(this.parseBytecode(bytecodeLines, ((BytecodeLineOffset) bytecodeLine).getOffset(), recList));
				return stmtSeq;

			case ifnull:
				stmtSeq.add(this.parseOpcodeIfnull((BytecodeLineOffset) bytecodeLine, bytecodeLines, recList));
				return stmtSeq;

			case ifne:
			case ifge:
			case ifgt:
			case ifle:
			case iflt:
			case ifeq:
				stmtSeq.add(this.parseOpcodeIfXX((BytecodeLineOffset) bytecodeLine, bytecodeLines, recList));
				return stmtSeq;

			case if_Xcmpne:
			case if_Xcmpge:
			case if_Xcmpgt:
			case if_Xcmple:
			case if_Xcmplt:
			case if_Xcmpeq:
				stmtSeq.add(this.parseOpcodeIf_XcmpXX((BytecodeLineOffset) bytecodeLine, bytecodeLines, recList));
				return stmtSeq;

			case fcmpg:
			case fcmpl:
				this.parseOpcodeFcmpX();
				break;
			case dcmpg:
			case dcmpl:
				this.parseOpcodeDcmpX();
				break;

			case _return:
				stmtSeq.setReturnStmt(this.parseOpcodeReturn());
				return stmtSeq;

			default:
				String message = "opcode \"" + bytecodeLine.getOpcode().getName() + "\" is not known";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
		} while (nextOffset > 0);

		/** should never happen; should always return statement in while-loop */
		String message = "bytecode of method should always return statement";
		Logger.getLogger(Decompiler.class).fatal(message);
		throw new DecompilerException(message);
	}

	/** opcode parsing methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * @param recList COMMENT
	 */
	private void parseBytecodeGetfield(BytecodeLineConstantTableAccessibleObject bytecodeLine, RecursionList recList) {
		Expression expr = this.stack.pop();
		if (expr.getResultType().isPrimitive()) {
			String message = "can not get field \"" + ((Field) bytecodeLine.getAccessibleObject()).getName() + "\" from constraint value \"" + expr + "\" of primitive type";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DisassemblerException(message);
		}

		this.stack.push(
				this.getFieldValue(bytecodeLine, expr, recList));
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 */
	private void parseOpcodeCheckcast(BytecodeLineConstantTableClass bytecodeLine) {
		Expression expr = this.stack.pop();
		if (!ClassUtils.isAssignable(expr.getResultType(), bytecodeLine.getType())) {
			String message = "could not cast from \"" + expr.getResultType().getSimpleName() + "\" to \"" + ((BytecodeLineConstantTableClass)bytecodeLine).getType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param opcode COMMENT
	 */
	private void parseOpcodeX2X(Opcode opcode) {
		Expression expr = this.stack.pop();

		if (opcode == Opcode.i2f && ClassUtils.isIntegerType(expr.getResultType())) {
			if (ExpressionUtils.isFinishedAtomExpr(expr, AtomIntegerExpr.class))
				this.stack.push(
						new AtomFloatExpr(((AtomIntegerExpr) expr).getValue().floatValue()));
			else
				this.stack.push(new PremClasscastExpr(expr, Keyword.i2f));
		} else if (opcode == Opcode.i2d && ClassUtils.isIntegerType(expr.getResultType())) {
			if (ExpressionUtils.isFinishedAtomExpr(expr, AtomIntegerExpr.class))
				this.stack.push(
						new AtomDoubleExpr(((AtomIntegerExpr) expr).getValue().doubleValue()));
			else
				this.stack.push(new PremClasscastExpr(expr, Keyword.i2d));
		} else if (opcode == Opcode.f2d && ClassUtils.isFloatType(expr.getResultType())) {
			if (ExpressionUtils.isFinishedAtomExpr(expr, AtomFloatExpr.class))
				this.stack.push(
						new AtomDoubleExpr(((AtomFloatExpr) expr).getValue().doubleValue()));
			else
				this.stack.push(new PremClasscastExpr(expr, Keyword.f2d));
		} else {
			String input = opcode == Opcode.i2f || opcode == Opcode.i2d ? "integer" : opcode == Opcode.f2d ? "float" : opcode.getName();
			String output = opcode == Opcode.i2f ? "float" : opcode == Opcode.i2d || opcode == Opcode.f2d ? "double" : opcode.getName();
			String message = "expected \"" + input + "\" but got \"" + expr + "\" resulting to type \"" + expr.getResultType().getSimpleName() + "\" to cast to \"" + output + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param opcode COMMENT
	 */
	private void parseOpcodeXrem(Opcode opcode) {
		Expression expr2 = this.stack.pop();
		Expression expr1 = this.stack.pop();

		if (opcode == Opcode.irem
				&& ClassUtils.isIntegerType(expr1.getResultType())
				&& ClassUtils.isIntegerType(expr2.getResultType())) {
			if (expr1 instanceof AtomIntegerExpr && expr2 instanceof AtomIntegerExpr) {
				int value1 = ((AtomIntegerExpr) expr1).getValue();
				int value2 = ((AtomIntegerExpr) expr2).getValue();
				this.stack.push(new AtomIntegerExpr(value1 - (value1 / value2) * value2));
			} else
				this.stack.push(new ArithmeticExpr(
						expr1, ArithmeticOperator.SUB,
						new ArithmeticExpr(
								new ArithmeticExpr(expr1, ArithmeticOperator.DIV, expr2),
								ArithmeticOperator.MUL, expr2)));
		} else if (opcode == Opcode.frem
				&& ClassUtils.isFloatType(expr1.getResultType())
				&& ClassUtils.isFloatType(expr2.getResultType())) {
			if (expr1 instanceof AtomFloatExpr && expr2 instanceof AtomFloatExpr) {
				float value1 = ((AtomFloatExpr) expr1).getValue();
				float value2 = ((AtomFloatExpr) expr2).getValue();
				this.stack.push(new AtomFloatExpr(value1 - (value2 * (value1 / value2))));
			} else
				this.stack.push(new ArithmeticExpr(
						expr1, ArithmeticOperator.SUB,
						new ArithmeticExpr(
								expr2, ArithmeticOperator.MUL,
								new PremMethodExpr(
										new ArithmeticExpr(expr1, ArithmeticOperator.DIV, expr2),
										intValueFloat, new ArrayList<Expression>()))));
		} else if (opcode == Opcode.drem
				&& ClassUtils.isDoubleType(expr1.getResultType())
				&& ClassUtils.isDoubleType(expr2.getResultType())) {
			if (expr1 instanceof AtomDoubleExpr && expr2 instanceof AtomDoubleExpr) {
				double value1 = ((AtomDoubleExpr) expr1).getValue();
				double value2 = ((AtomDoubleExpr) expr2).getValue();
				this.stack.push(new AtomDoubleExpr(value1 - (value2 * (value1 / value2))));
			} else
				this.stack.push(new ArithmeticExpr(
						expr1, ArithmeticOperator.SUB,
						new ArithmeticExpr(
								expr2, ArithmeticOperator.MUL,
								new PremMethodExpr(
										new ArithmeticExpr(expr1, ArithmeticOperator.DIV, expr2),
										intValueDouble, new ArrayList<Expression>()))));
		} else if (opcode == Opcode.lrem
				&& ClassUtils.isLongType(expr1.getResultType())
				&& ClassUtils.isLongType(expr2.getResultType())) {
			String message = "opcode lrem not supported since long values are handled as integer values";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		} else {
			String message = "unsupported remainder opcode \"" + opcode.getName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 */
	private void parseOpcodeLdcX(BytecodeLineSimpleValue bytecodeLine) {
		if (ClassUtils.isDoubleType(bytecodeLine.getValue().getClass()))
			this.stack.push(new AtomDoubleExpr((Double) bytecodeLine.getValue()));
		else if (ClassUtils.isFloatType(bytecodeLine.getValue().getClass()))
			this.stack.push(new AtomFloatExpr((Float) bytecodeLine.getValue()));
		else if (ClassUtils.isIntegerType(bytecodeLine.getValue().getClass()))
			this.stack.push(new AtomIntegerExpr((Integer) bytecodeLine.getValue()));
		else if (bytecodeLine.getValue().getClass().equals(String.class))
			this.stack.push(new AtomStringExpr((String) bytecodeLine.getValue()));
		else
			this.stack.push(new AtomObjectExpr(bytecodeLine.getValue()));
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 */
	private void parseOpcodeXArithmetic(BytecodeLineSimple bytecodeLine) {
		Expression expr2 = this.stack.pop();
		Expression expr1 = this.stack.pop();
		this.stack.push(this.getCalculatedValue(expr1, ArithmeticOperator.fromOpcode(bytecodeLine.getOpcode()), expr2));
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLineTableswitch COMMENT
	 * @param bytecodeLines COMMENT
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private StatementSeq parseOpcodeTableSwitch(BytecodeLineTableswitch bytecodeLineTableswitch, Map<Integer, BytecodeLine> bytecodeLines, RecursionList recList) {
		Expression expr = this.stack.pop();

		if (expr instanceof AtomIntegerExpr) {
			Integer caseOffset;
			if ((caseOffset = bytecodeLineTableswitch.getOffsetsMap().get(((AtomIntegerExpr) expr).getValue().toString())) == null
					&& (caseOffset = bytecodeLineTableswitch.getOffsetsMap().get("default")) == null) {
				String message = "neither a case for value \"" + ((AtomIntegerExpr) expr).getValue() + "\" nor a default case is defined.";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			} else
				return this.parseBytecode(bytecodeLines, caseOffset, recList);
		} else
			return this.getTableswitchConstraint(
					expr, bytecodeLineTableswitch.getOffsetsMap(), bytecodeLineTableswitch.getOffsetsMap().keySet().iterator(), bytecodeLineTableswitch.getOffsetsMap().get("default"), bytecodeLines, recList);
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 */
	private void parseOpcodeInvokeX(BytecodeLineConstantTableAccessibleObject bytecodeLine) {
		/* get arguments for method or constructor */
		ArgumentList argumentValues = this.getArgumentList(bytecodeLine.getAccessibleObject());

		/* pop value from stack */
		Expression expr;
		if (bytecodeLine.getOpcode() == Opcode.invokestatic)
			expr = new AtomClassExpr(((Method) bytecodeLine.getAccessibleObject()).getDeclaringClass());
		else
			expr = this.stack.pop();

		/* no premature value and accessible object is a method that can get invoked */
		if (!argumentValues.hasPrematureArgument()
				&& ((expr instanceof AtomExpr<?> && ((AtomExpr<?>) expr).isFinishedType())
						|| expr instanceof AtomClassExpr)) {
			/* get argument values from expression in argument list */
			Object[] arguments = new Object[argumentValues.size()];
			for (int i=0; i<argumentValues.size(); i++)
				arguments[i] = ((AtomExpr<?>) argumentValues.get(i)).getValue();

			/* invoke the method with the object and the arguments from this stack */
			this.stack.push(
					this.invokeAccessibleObject(bytecodeLine, bytecodeLine.getOpcode() == Opcode.invokestatic ? new AtomObjectExpr(null) : (AtomExpr<?>) expr, arguments));
		}
		/* accessible object is a method and class file can get loaded from the classloader */
		else if (bytecodeLine.getAccessibleObject() instanceof Method
				&& this.isDecompilable((Method) bytecodeLine.getAccessibleObject())
				&& !this.isPreparedByDialect((Method) bytecodeLine.getAccessibleObject())) {
			/* disassemble the method that should be invoked */
			DisassembledMethod disassembledSubMethod = Disassembler.disassemble((Method) bytecodeLine.getAccessibleObject());
			PremStmtSeqExpr stmtSeqExpr = new PremStmtSeqExpr(new Decompiler()
					.decompile(disassembledSubMethod.getBytecodeLines(), this.depth+1, expr, argumentValues.toArray(new Expression[0])));

			/* embed the return value of the disassembled method to the invocation value */
			this.stack.push(stmtSeqExpr);
		}
		/* class file can not get loaded from the classloader (e.g. java.lang classes) or is preparable by the dialect */
		else {
			if (bytecodeLine.getAccessibleObject() instanceof Field)
				this.stack.push(new PremFieldExpr(
						expr, (Field) bytecodeLine.getAccessibleObject()));
			else if (bytecodeLine.getAccessibleObject() instanceof Method)
				this.stack.push(new PremMethodExpr(
						expr, (Method) bytecodeLine.getAccessibleObject(), argumentValues));
			else if (bytecodeLine.getAccessibleObject() instanceof Constructor<?>)
				this.stack.push(new PremConstructorExpr(
						expr, (Constructor<?>) bytecodeLine.getAccessibleObject(), argumentValues));
			else {
				String message = "can not parse opcode \"" + bytecodeLine.getOpcode().getName() + "\" with accessible object \"" + bytecodeLine.getAccessibleObject() + "\" of type \"" + bytecodeLine.getAccessibleObject().getClass().getSimpleName() + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
		}
	}

	/**
	 * COMMENT
	 * 
	 *  @param bytecodeLine COMMENT
	 */
	private void parseOpcodeXNewarray(Class<?> type) {
		Expression arrayLengthExpr = this.stack.pop();
		if (ExpressionUtils.isFinishedAtomExpr(arrayLengthExpr, AtomIntegerExpr.class))
			this.stack.push(
					new AtomArrayExpr<>(type, ((AtomIntegerExpr) arrayLengthExpr).getValue()));
		else {
			String message = "can not create array with length \"" + arrayLengthExpr + "\" resulting in \"" + arrayLengthExpr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 */
	private void parseOpcodeArraylength() {
		Expression expr = this.stack.pop();
		if (ExpressionUtils.isFinishedAtomExpr(expr, AtomObjectExpr.class)
				&& ((AtomObjectExpr) expr).getResultType().isArray()) {
			this.stack.push(
					new AtomIntegerExpr(
							Array.getLength(((AtomObjectExpr) expr).getValue())));
		} else if(expr.getResultType().isArray())
			this.stack.push(
					new PremArraylengthExpr(expr));
		else {
			String message = "expected expression of array type, but got \"" + expr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 */
	private void parseOpcodeXaload() {
		/* the designator index for the array (expected) */
		Expression expr1 = this.stack.pop();
		if (!ClassUtils.isIntegerType(expr1.getResultType())) {
			String message = "unexpected expression of type \"" + expr1.getClass().getSimpleName() + "\" as array index";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
		/* the array (expected) */
		Expression expr2 = this.stack.pop();
		if (!expr2.getResultType().isArray()) {
			String message = "unexpected expression of type \"" + expr2.getClass().getSimpleName() + "\" as array";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}

		if (ExpressionUtils.isFinishedAtomExpr(expr1, AtomIntegerExpr.class)
				&& ExpressionUtils.isFinishedAtomExpr(expr2, AtomObjectExpr.class))
			this.stack.push(this.getAtomExprFromValue(Array.get(
					((AtomObjectExpr) expr2).getValue(),
					((AtomIntegerExpr) expr1).getValue())));
		else if (ExpressionUtils.isFinishedAtomExpr(expr1, AtomIntegerExpr.class)
				&& expr2 instanceof AtomArrayExpr<?>)
			this.stack.push(((AtomArrayExpr<?>) expr2).get(((AtomIntegerExpr) expr1).getValue()));
		else
			this.stack.push(new PremArrayelementExpr(expr2, expr1));
	}

	/**
	 * COMMENT
	 */
	private void parseOpcodeXastore() {
		Expression valueExpr = this.stack.pop();
		Expression indexExpr = this.stack.pop();
		Expression arrayExpr = this.stack.pop();

		if (!(arrayExpr instanceof AtomArrayExpr<?>)) {
			String message = "can not store expression \"" + valueExpr + "\" to index \"" + indexExpr + "\" in non-array expression \"" + arrayExpr + "\" of type \"" + arrayExpr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}

		if (!(indexExpr instanceof AtomIntegerExpr)
				|| !((AtomIntegerExpr) indexExpr).isFinishedType()) {
			String message = "can not store expression \"" + valueExpr + "\" to non-finished index \"" + indexExpr + "\" in array expression \"" + arrayExpr + "\" of type \"" + arrayExpr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}

		if (!ClassUtils.isCastOrAssignable(((AtomArrayExpr<?>) arrayExpr).getType(), valueExpr.getResultType())) {
			String message = "can not store non-matching expression \"" + valueExpr + "\" to index \"" + indexExpr + "\" in array expression \"" + arrayExpr + "\" of type \"" + arrayExpr.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}

		((AtomArrayExpr<?>) arrayExpr).set(((AtomIntegerExpr) indexExpr).getValue(), valueExpr);
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * @param bytecodeLines COMMENT
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private StatementSeq parseOpcodeIfXX(BytecodeLineOffset bytecodeLine, Map<Integer,BytecodeLine> bytecodeLines, RecursionList recList) {
		Expression expr = this.stack.pop();

		BoolExpression boolExpr = ExpressionUtils.compareExpressions(
				expr, CompareOperator.fromOpcode(bytecodeLine.getOpcode().getName()), new AtomIntegerExpr(0));

		if (boolExpr instanceof AtomBoolExpr) {
			if (((AtomBoolExpr) boolExpr).getValue())
				return this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), recList);
			else
				return this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList);
		} else {
			if (bytecodeLine.getLineNumber() > bytecodeLine.getOffset()) {
				if (!recList.isCurrentRecursion(bytecodeLine)) {
					RecursionList extendedRecList = recList.clone();
					extendedRecList.add(bytecodeLine);
					StatementSeq loopedSeq = new StatementSeq(this.depth);
					loopedSeq.add(new LoopStmt(boolExpr,
									this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), extendedRecList)));
					loopedSeq.add(this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList.clone()));
					return loopedSeq;
				} else
					return new StatementSeq(this.depth);
			} else
				return new StatementSeq(this.depth, new IfThenElseStmt(
						boolExpr,
						this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), recList.clone()),
						this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList.clone())));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * @param bytecodeLines COMMENT
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private StatementSeq parseOpcodeIf_XcmpXX(BytecodeLineOffset bytecodeLine, Map<Integer,BytecodeLine> bytecodeLines, RecursionList recList) {
		Expression expr2 = this.stack.pop();
		Expression expr1 = this.stack.pop();

		BoolExpression boolExpr = ExpressionUtils.compareExpressions(
				expr1, CompareOperator.fromOpcode(bytecodeLine.getOpcode().getName()), expr2);

		if (boolExpr instanceof AtomBoolExpr) {
			if (((AtomBoolExpr) boolExpr).getValue())
				return this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), recList);
			else
				return this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList);
		} else {
			if (bytecodeLine.getLineNumber() > bytecodeLine.getOffset()) {
				if (!recList.isCurrentRecursion(bytecodeLine)) {
					RecursionList extendedRecList = recList.clone();
					extendedRecList.add(bytecodeLine);
					StatementSeq loopedSeq = new StatementSeq(this.depth);
					loopedSeq.add(new LoopStmt(boolExpr, this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), extendedRecList)));
					loopedSeq.add(this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList.clone()));
					return loopedSeq;
				} else
					return new StatementSeq(this.depth);
			} else
				return new StatementSeq(this.depth, new IfThenElseStmt(
						boolExpr,
						this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), recList.clone()),
						this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList.clone())));
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * @param bytecodeLines COMMENT
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private StatementSeq parseOpcodeIfnull(BytecodeLineOffset bytecodeLine, Map<Integer, BytecodeLine> bytecodeLines, RecursionList recList) {
		Expression expr = this.stack.pop();

		if (expr instanceof AtomExpr<?>
				&& ((AtomExpr<?>) expr).isFinishedType()) {
			if (((AtomExpr<?>) expr).getValue() == null)
				return this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), recList);
			else
				return this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList);
		} else {
			/* skip null-checks for variable fields (might be null, will be set by solver-result) */
			if (expr instanceof AtomExpr<?> && ((AtomExpr<?>) expr).isVariable()
					|| expr instanceof PremGetfieldExpr && ((PremGetfieldExpr) expr).isVariable())
				return this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList);
			else {
				if (bytecodeLine.getLineNumber() > bytecodeLine.getOffset()) {
					if (!recList.isCurrentRecursion(bytecodeLine)) {
						RecursionList extendedRecList = recList.clone();
						extendedRecList.add(bytecodeLine);
						StatementSeq loopedSeq = new StatementSeq(this.depth);
						loopedSeq.add(new LoopStmt(new CompareExpr(expr, CompareOperator.EQUAL, new AtomObjectExpr(null)),
										this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), extendedRecList)));
						loopedSeq.add(this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList.clone()));
						return loopedSeq;
					} else
						return new StatementSeq(this.depth);
				} else
					return new StatementSeq(this.depth, new IfThenElseStmt(
							new CompareExpr(expr, CompareOperator.EQUAL, new AtomObjectExpr(null)),
							this.parseBytecode(bytecodeLines, bytecodeLine.getOffset(), recList.clone()),
							this.parseBytecode(bytecodeLines, bytecodeLine.getFollowingLineNumber(), recList.clone())));
			}
		}
	}

	/**
	 * COMMENT
	 */
	private void parseOpcodeFcmpX() {
		Expression expr2 = this.stack.pop();
		Expression expr1 = this.stack.pop();

		if (ClassUtils.isFloatType(expr1.getResultType())
				&& ClassUtils.isFloatType(expr2.getResultType())) {
			if (ExpressionUtils.isFinishedAtomExpr(expr1, AtomFloatExpr.class)
					&& ExpressionUtils.isFinishedAtomExpr(expr2, AtomFloatExpr.class))
				this.stack.push(new AtomIntegerExpr(
						((AtomFloatExpr) expr1).compareTo((AtomFloatExpr) expr2)));
			else
				this.stack.push(
						new ArithmeticExpr(
								expr1, ArithmeticOperator.SUB, expr2));
		} else {
			String message = "expected float values but got \"" + expr1.getResultType().getSimpleName() + "\" and \"" + expr2.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 */
	private void parseOpcodeDcmpX() {
		Expression expr2 = this.stack.pop();
		Expression expr1 = this.stack.pop();

		if (ClassUtils.isDoubleType(expr1.getResultType())
				&& ClassUtils.isDoubleType(expr2.getResultType())) {
			if (ExpressionUtils.isFinishedAtomExpr(expr1, AtomDoubleExpr.class)
					&& ExpressionUtils.isFinishedAtomExpr(expr2, AtomDoubleExpr.class))
				this.stack.push(new AtomIntegerExpr(
						((AtomDoubleExpr) expr1).compareTo((AtomDoubleExpr) expr2)));
			else
				this.stack.push(
						new ArithmeticExpr(
								expr1, ArithmeticOperator.SUB, expr2));
		} else {
			String message = "expected double values but got \"" + expr1.getResultType().getSimpleName() + "\" and \"" + expr2.getResultType().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private ReturnStmt parseOpcodeReturn() {
		return new ReturnStmt(this.stack.pop());
	}

	/** tableswitch
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param offsetsMap COMMENT
	 * @param offsetsMapKeyIterator COMMENT
	 * @param defaultOffset COMMENT
	 * @param bytecodeLines COMMENT
	 * @param prefixedFields COMMENT
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private StatementSeq getTableswitchConstraint(Expression expr, Map<String, Integer> offsetsMap, Iterator<String> offsetsMapKeyIterator, Integer defaultOffset, Map<Integer, BytecodeLine> bytecodeLines, RecursionList recList) {
		if (offsetsMapKeyIterator.hasNext()) {
			String offsetsKey = offsetsMapKeyIterator.next();
			if (offsetsKey.matches("\\d+"))
				return new StatementSeq(this.depth, new IfThenElseStmt(
						new CompareExpr(expr, CompareOperator.EQUAL,
								new AtomIntegerExpr(Integer.parseInt(offsetsKey))),
						this.parseBytecode(bytecodeLines, offsetsMap.get(offsetsKey), recList),
						this.getTableswitchConstraint(expr, offsetsMap, offsetsMapKeyIterator, defaultOffset, bytecodeLines, recList)));
			else if (offsetsKey.equals("default"))
				return this.getTableswitchConstraint(expr, offsetsMap, offsetsMapKeyIterator, defaultOffset, bytecodeLines, recList);
			else {
				String message = "case of a tableswitch needs to be integer or default case but is \"" + offsetsKey + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DisassemblerException(message);
			}
		} else {
			if (defaultOffset != null)
				return this.parseBytecode(bytecodeLines, defaultOffset, recList);
			else
				return new StatementSeq(this.depth, new ReturnStmt(new AtomBoolExpr(false)));
		}
	}

	/** expressions getters
	 * ----- ----- ----- ----- ----- */

	/**
	 * getCalculatedValue returns an expression for the given expressions and
	 *  the arithmetic operator. If the expressions are both atomar the
	 *  new atomar expression is calculated, otherwise a new expression formula
	 *  is returned.
	 * 
	 * @param expr1 the first expression
	 * @param operator the arithmetic operator to calculate the expression
	 * @param expr1 the second expression
	 * 
	 * @return the calculated value as an atomar expression if both expressions
	 *  are atomar, a new expression formula with the expression and the
	 *  arithmetic operator otherwise
	 */
	private Expression getCalculatedValue(Expression expr1, ArithmeticOperator operator, Expression expr2) {
		expr1 = expr1.evaluate(new ComponentVariables(null));
		expr2 = expr2.evaluate(new ComponentVariables(null));
		if (expr1 instanceof AtomExpr<?> && ((AtomExpr<?>) expr1).isFinishedNumberType()
				&& expr2 instanceof AtomExpr<?> && ((AtomExpr<?>) expr2).isFinishedNumberType())
			return ((AtomExpr<?>) expr1).calc(((AtomExpr<?>) expr2), operator);
		else
			return new ArithmeticExpr(expr1, operator, expr2);
	}

	/**
	 * COMMENT
	 * 
	 * @param object COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomExpr<?> getAtomExprFromValue(Object object) {
		if (ClassUtils.isIntegerType(object.getClass()))
			return new AtomIntegerExpr((Integer) object);
		else if (ClassUtils.isFloatType(object.getClass()))
			return new AtomFloatExpr((Float) object);
		else if (ClassUtils.isDoubleType(object.getClass()))
			return new AtomDoubleExpr((Double) object);
		else if (ClassUtils.isBooleanType(object.getClass()))
			return new AtomIntegerExpr(((Boolean) object).equals(true) ? 1 : 0);
		else
			return new AtomObjectExpr(object);
	}

	/** invocation
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * @param expr COMMENT
	 * @param arguments COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomExpr<?> invokeAccessibleObject(BytecodeLineConstantTableAccessibleObject bytecodeLine, Expression expr, Object[] arguments) {
		AccessibleObject accessibleObject = bytecodeLine.getAccessibleObject();

		/** COMMENT */
		if (accessibleObject instanceof Method) {
			Object invokationObject;
			if (bytecodeLine.getOpcode() != Opcode.invokestatic
					&& expr instanceof AtomExpr<?>
					&& ClassUtils.classesEquals(
							((AtomExpr<?>) expr).getValue().getClass(),
							((Method) accessibleObject).getDeclaringClass()))
				invokationObject = ((AtomExpr<?>) expr).getValue();
			else if (bytecodeLine.getOpcode() == Opcode.invokestatic && expr instanceof AtomClassExpr)
				invokationObject = null;
			else {
				String message = "could not get invokation object for accessible object \"" + accessibleObject + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
				
			Method lineMethod = (Method) accessibleObject;

			/* try to invoke method */
			try {
				/* push result of invoked method to stack */
				if (ClassUtils.isDoubleType(lineMethod.getReturnType()))
					return new AtomDoubleExpr(
							(Double) lineMethod.invoke(invokationObject, arguments));
				else if (ClassUtils.isFloatType(lineMethod.getReturnType()))
					return new AtomFloatExpr(
							(Float) lineMethod.invoke(invokationObject, arguments));
				else if (ClassUtils.isIntegerType(lineMethod.getReturnType()))
					return new AtomIntegerExpr(
							(Integer) lineMethod.invoke(invokationObject, arguments));
				else
					return new AtomObjectExpr(
							lineMethod.invoke(invokationObject, arguments));
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
				String message = "could not invoke method \"" + lineMethod.toGenericString().replaceAll(".*\\s(\\S+)$", "$1") + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
		}
		/* COMMENT */
		else if (accessibleObject instanceof Constructor<?>
				&& bytecodeLine.getOpcode() != Opcode.invokestatic
				&& expr instanceof AtomClassExpr
				&& ClassUtils.classesEquals(
						((AtomClassExpr) expr).getValue(),
						((Constructor<?>) accessibleObject).getDeclaringClass())) {
			Constructor<?> lineConstructor = (Constructor<?>) accessibleObject;

			/* pop unused duplicated atomar class expression object */
			this.stack.pop();

			/* try to instantiate class */
			try {
				/* push new instantiation of class to stack */
				if (ClassUtils.isDoubleType(lineConstructor.getDeclaringClass()))
					return new AtomDoubleExpr(
							(Double) lineConstructor.newInstance(arguments));
				else if (ClassUtils.isFloatType(lineConstructor.getDeclaringClass()))
					return new AtomFloatExpr(
							(Float) lineConstructor.newInstance(arguments));
				else if (ClassUtils.isIntegerType(lineConstructor.getDeclaringClass()))
					return new AtomIntegerExpr(
							(Integer) lineConstructor.newInstance(arguments));
				else
					return new AtomObjectExpr(
							lineConstructor.newInstance(arguments));
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | InstantiationException e) {
				String message = "could not instantiate new \"" + lineConstructor.getDeclaringClass().getName() + "\" \"" + lineConstructor.getName() + "\"";
				Logger.getLogger(Decompiler.class).fatal(message);
				throw new DecompilerException(message);
			}
		}
		/* COMMENT */
		else {
			String message = "no valid access to accessible object \"" + accessibleObject + "\" of type \"" + accessibleObject.getClass().getSimpleName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/** field value getters
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * @param expr COMMENT
	 * @param recList COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression getFieldValue(BytecodeLineConstantTableAccessibleObject bytecodeLine, Expression expr, RecursionList recList) {
		return new PremGetfieldExpr(expr, (Field) bytecodeLine.getAccessibleObject());
	}

	/**
	 * COMMENT
	 * 
	 * @param bytecodeLine COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression getStaticFieldValue(BytecodeLineConstantTableAccessibleObject bytecodeLine, RecursionList recList) {
		Field bytecodeLineField = (Field) bytecodeLine.getAccessibleObject();

		/** non-variable static field */
		if (bytecodeLineField.getAnnotation(Variable.class) == null)
			return new PremGetfieldExpr(new AtomObjectExpr(null), bytecodeLineField);
		/** variable static field */
		else {
			String message = "cannot handle variable static field \"" + bytecodeLineField.getName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param method COMMENT
	 * 
	 * @return COMMENT
	 */
	private boolean isDecompilable(Method method) {
		return method.getDeclaringClass().getClassLoader() != null;
	}

	/**
	 * COMMENT
	 * 
	 * @param method COMMENT
	 * 
	 * @return COMMENT
	 */
	private boolean isPreparedByDialect(Method method) {
		return method.getAnnotation(PreparableMethod.class) != null;
	}

	/** argument list
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param accessibleObject COMMENT
	 * 
	 * @return COMMENT
	 */
	private ArgumentList getArgumentList(AccessibleObject accessibleObject) {
		/** get count of parameters */
		int parameterCount;
		if (accessibleObject instanceof Method)
			parameterCount = ((Method) accessibleObject).getParameterTypes().length;
		else if (accessibleObject instanceof Constructor<?>)
			parameterCount = ((Constructor<?>) accessibleObject).getParameterTypes().length;
		else {
			String message = "accessible object needs to be method or constructor but is \"" + accessibleObject.getClass().getName() + "\"";
			Logger.getLogger(Decompiler.class).fatal(message);
			throw new DecompilerException(message);
		}

		/** pop argument values from stack */
		ArgumentList argumentValues = new ArgumentList();
		for (int i=0; i<parameterCount; i++) {
			Expression argument = this.stack.pop();
			if (!argumentValues.hasPrematureArgument()
					&& (!(argument instanceof AtomExpr<?>)
							|| !((AtomExpr<?>) argument).isFinishedType()))
				argumentValues.setHasPrematureArgument(true);
			argumentValues.add(argument);
		}
		Collections.reverse(argumentValues);

		return argumentValues;
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class ArgumentList extends ArrayList<Expression> {
		/** COMMENT */
		private static final long serialVersionUID = 4116003574027287498L;

		/** COMMENT */
		private boolean hasPrematureArgument;

		/**
		 * COMMENT
		 */
		public ArgumentList() {
			this.hasPrematureArgument = false;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public boolean hasPrematureArgument() {
			return this.hasPrematureArgument;
		}

		/**
		 * COMMENT
		 * 
		 * @param hasPrematureArgument COMMENT
		 */
		public void setHasPrematureArgument(boolean hasPrematureArgument) {
			this.hasPrematureArgument = hasPrematureArgument;
		}
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class RecursionList {
		/** COMMENT */
		private RecursionElement last;

		/**
		 * COMMENT
		 */
		public RecursionList() {
			this.last = null;
		}

		/**
		 * COMMENT
		 * 
		 * @param bytecodeLine COMMENT
		 */
		public void add(BytecodeLineOffset bytecodeLine) {
			this.last = new RecursionElement(bytecodeLine.getOffset(), bytecodeLine.getLineNumber(), this.last);
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public boolean remove() {
			if (this.isEmpty())
				return false;
			else {
				this.last = this.last.prev;
				return true;
			}
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public boolean isEmpty() {
			return this.last == null;
		}

		/**
		 * COMMENT
		 * 
		 * @param bytecodeLine COMMENT
		 * 
		 * @return COMMENT
	 */
		public boolean isCurrentRecursion(BytecodeLineOffset bytecodeLine) {
			return this.last != null
					&& this.last.start == bytecodeLine.getOffset()
					&& this.last.end == bytecodeLine.getLineNumber();
		}

		/**
		 * COMMENT
		 * 
		 * @param index COMMENT
		 * 
		 * @return COMMENT
	 */
		public boolean skipsCurrentRecursion(int index) {
			return this.last != null && this.last.end < index;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public RecursionList clone() {
			RecursionList recursionList = new RecursionList();
			if (this.last != null)
				recursionList.last = this.last.clone();
			return recursionList;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
	 */
		public String toString() {
			StringBuilder stringBuilder = new StringBuilder();
			stringBuilder.append("[");
			RecursionElement recElem = this.last;
			while (recElem != null) {
				stringBuilder.append(recElem.toString());
				if (stringBuilder.length() > 1)
					stringBuilder.append(", ");
				recElem = recElem.prev;
			}
			stringBuilder.append("]");
			return stringBuilder.toString();
		}

		/**
		 * COMMENT
		 * 
		 * @author Max Nitze
		 */
		private static class RecursionElement {
			/** COMMENT */
			private int start;
			/** COMMENT */
			private int end;

			/** COMMENT */
			private RecursionElement prev;

			/**
			 * COMMENT
			 * 
			 * @param start COMMENT
			 * @param end COMMENT
			 */
			public RecursionElement(int start, int end, RecursionElement prev) {
				this.start = start;
				this.end = end;
				this.prev = prev;
			}

			/**
			 * COMMENT
			 * 
			 * @return COMMENT
	 */
			public RecursionElement clone() {
				return new RecursionElement(this.start, this.end, this.prev == null ? null : this.prev.clone());
			}

			/**
			 * COMMENT
			 * 
			 * @return COMMENT
	 */
			public String toString() {
				return "(" + this.start + "-->" + this.end + ")";
			}
		}
	}
}
