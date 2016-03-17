package de.agra.fomeja.backends;

/* imports */
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.RatNum;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.Z3Exception;

import de.agra.fomeja.backends.datatypes.ResultModel;
import de.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomBooleanExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomEnumExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.NotExpr;
import de.agra.fomeja.decompiling.expressions.premature.PremAccessibleObjectExpr;
import de.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr;
import de.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.agra.fomeja.exceptions.DialectException;
import de.agra.fomeja.exceptions.SatisfyException;
import de.agra.fomeja.preprocessing.ConstraintPreprocessor;
import de.agra.fomeja.preprocessing.std.StringCharAtPreprocessor;
import de.agra.fomeja.preprocessing.std.StringEqualsPreprocessor;
import de.agra.fomeja.preprocessing.std.StringLengthPreprocessor;
import de.agra.fomeja.preprocessing.std.StringMethodsPreprocessor;
import de.agra.fomeja.preprocessing.std.StringStartsWithPreprocessor;
import de.agra.fomeja.preprocessing.std.StringToCharArrayPreprocessor;
import de.agra.fomeja.types.BooleanConnector;
import de.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class SMTIIJava extends Dialect<BoolExpr, ArithExpr> {
	/** COMMENT */
	private static final Pattern stringResultPattern = Pattern.compile("^string-(?<name>.*)-c(?<char>\\d+)$");

	/** COMMENT */
	private Context context;

	/** COMMENT */
	private ConstraintPreprocessor constraintPreprocessor;

	/** COMMENT */
	private Set<String> atomBooleanExprSet;
	/** COMMENT */
	private Set<String> atomCharacterExprSet;
	/** COMMENT */
	private List<BoolExpr> curBoolExprs;

	/**
	 * COMMENT
	 */
	public SMTIIJava() {
		super(Type.smt2);

		try {
			this.context = new Context();
		} catch (Z3Exception e) {
			String message = "could not instantiate SMTIIJava due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}

		this.constraintPreprocessor = new ConstraintPreprocessor();
		this.constraintPreprocessor.register(new StringLengthPreprocessor());
		this.constraintPreprocessor.register(new StringEqualsPreprocessor());
		this.constraintPreprocessor.register(new StringCharAtPreprocessor());
		this.constraintPreprocessor.register(new StringStartsWithPreprocessor());
		this.constraintPreprocessor.register(new StringToCharArrayPreprocessor());
		this.constraintPreprocessor.register(new StringMethodsPreprocessor());

		this.atomBooleanExprSet = new HashSet<String>();
		this.atomCharacterExprSet = new HashSet<String>();
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Context getContext() {
		return this.context;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public List<BoolExpr> format(List<BoolExpression> boolExprs) throws SatisfyException {
		BoolExpression boolExpr = this.constraintPreprocessor.prepare(boolExprs);

		List<BoolExpr> formattedBoolExprs = new ArrayList<BoolExpr>();
		this.curBoolExprs = new ArrayList<BoolExpr>();
		this.curBoolExprs.add(this.getBackendBoolExpression(boolExpr));

		try {
			formattedBoolExprs.add(this.context.mkAnd(this.curBoolExprs.toArray(new BoolExpr[0])));
		} catch (Z3Exception e) {
			String message = "could not prepare all constraints due to z3 exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}

		return formattedBoolExprs;
	}

	@Override
	public ResultModel parseResult(Object resultObject) {
		if (resultObject instanceof Model) {
			Model model = (Model) resultObject;

//			System.out.println("\nSMTIIJava#parseResult: model =\n" + model); // TODO remove output

			ResultModel resultModel = new ResultModel();
			Map<String, int[]> stringResults = new HashMap<String, int[]>();

			try {
				for (FuncDecl constDecl : model.getConstDecls()) {
					Expr resultExpression = model.getConstInterp(constDecl);
					if (resultExpression.isReal()) {
						RatNum rationalNumber = (RatNum) resultExpression;
						resultModel.put(constDecl.getName().toString(), new Double(rationalNumber.getBigIntNumerator().doubleValue() / rationalNumber.getBigIntDenominator().doubleValue()));
					} else if (resultExpression.isInt()) {
						Matcher stringResultMatcher = stringResultPattern.matcher(constDecl.getName().toString());
						if (stringResultMatcher.matches()) {
							String stringName = stringResultMatcher.group("name");
							int maxStringLength = this.constraintPreprocessor.getMaxLength(stringName);
							int charPosition = Integer.parseInt(stringResultMatcher.group("char"));

							if (charPosition < maxStringLength) {
								if (stringResults.get(stringName) == null)
									stringResults.put(stringName, new int[maxStringLength]);
								int charValue = ((IntNum) resultExpression).getInt();
								stringResults.get(stringName)[charPosition] = charValue;
							}
						} else
							resultModel.put(constDecl.getName().toString(), ((IntNum) resultExpression).getInt());
					} else {
						String message = "result expression of unsupported type \"" + resultExpression.toString() + "\"";
						Logger.getLogger(SMTIIJava.class).error(message);
						System.err.println(message);
					}
				}
			} catch (Z3Exception e) {
				String message = "could not get constant declarations from result model: " + e.getMessage();
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new DialectException(message);
			}

			for (Map.Entry<String, int[]> stringResult : stringResults.entrySet()) {
				int firstNegIndex = stringResult.getValue().length;
				for (int i=0; i<stringResult.getValue().length; i++) {
					if (stringResult.getValue()[i] < 0) {
						firstNegIndex = i;
						break;
					}
				}

				char[] characters = new char[firstNegIndex];
				for (int i=0; i<characters.length; i++)
					characters[i] = (char) stringResult.getValue()[i];

				resultModel.put(stringResult.getKey(), new String(characters));
			}

			// TODO remove output
//			System.out.println("\nSMTIIJava#parseResult: resultMap =");
//			for (Map.Entry<String, Object> result : resultModel.entrySet()) {
//				if (result.getValue() instanceof String) {
//					System.out.print(result.getKey() + " = ");
//					for (char c : ((String) result.getValue()).toCharArray()) {
//						if (c != 0)
//							System.out.print(c);
//						else
//							System.out.print("\\0");
//					}
//					System.out.println(" with length " + ((String) result.getValue()).length());
//				} else
//					System.out.println(result.getKey() + " = " + result.getValue());
//			}

			return resultModel;
		} else {
			String message = "result object needs to be model but is \"" + resultObject.getClass().getSimpleName() + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/** overridden bool expression methods
	 * ----- ----- ----- ----- ----- ----- */

	@Override
	public BoolExpr prepareAtomBoolExpr(AtomBoolExpr boolExpr) {
		try {
			return this.context.mkBool(boolExpr.getValue());
		} catch (Z3Exception e) {
			String message = "could not make boolean expression from boolean constraint \"" + boolExpr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public BoolExpr prepareNotExpr(NotExpr boolExpr) {
		try {
			return this.context.mkNot(this.getBackendBoolExpression(boolExpr.getBoolExpr()));
		} catch (Z3Exception e) {
			String message = "could not negotiate boolean expression \"" + boolExpr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public BoolExpr prepareCompareExpr(CompareExpr boolExpr) {
		try {
			ArithExpr arithExpr1 = this.getBackendExpression(boolExpr.getExpr1());
			ArithExpr arithExpr2 = this.getBackendExpression(boolExpr.getExpr2());

			switch (boolExpr.getOperator()) {
			case EQUAL:
				return this.context.mkEq(arithExpr1, arithExpr2);
			case GREATER:
				return this.context.mkGt(arithExpr1, arithExpr2);
			case GREATER_EQUAL:
				return this.context.mkGe(arithExpr1, arithExpr2);
			case LESS:
				return this.context.mkLt(arithExpr1, arithExpr2);
			case LESS_EQUAL:
				return this.context.mkLe(arithExpr1, arithExpr2);
			case NOT_EQUAL:
				return this.context.mkNot(this.context.mkEq(arithExpr1, arithExpr2));
			default:
				String message = "constraint operator \"" + boolExpr.getOperator().getAsciiName() + "\" is not known";
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new DialectException(message);
			}
		} catch (Z3Exception e) {
			String message = "could not prepare compare expression \"" + boolExpr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public BoolExpr prepareChainedBoolExpr(ConnectedBoolExpr boolExpr) {
		BoolExpr[] boolExprs = new BoolExpr[boolExpr.getBoolExprs().size()];
		int i = 0;
		for (BoolExpression constraint : boolExpr.getBoolExprs())
			boolExprs[i++] = this.getBackendBoolExpression(constraint);

		try {
			switch (boolExpr.getConnector()) {
			case AND:
				return this.context.mkAnd(boolExprs);
			case OR:
				return this.context.mkOr(boolExprs);
			default:
				String message = "boolean connector \"" + boolExpr.getConnector().getCode() + "\" is not known";
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new DialectException(message);
			}
		} catch (Z3Exception e) {
			String message = "could not prepare connected boolean constraint set \"" + boolExpr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public BoolExpr prepareBoolIfThenElseExpr(BoolIfThenElseExpr boolExpr) {
		try {
			BoolExpr lastITE = this.getBackendBoolExpression(boolExpr.getElseCaseExpr());
			for (int i=boolExpr.getCondBoolExprPairs().size()-1; i>=0; i--) {
				lastITE = (BoolExpr) this.context.mkITE(
						this.getBackendBoolExpression(boolExpr.getCondBoolExprPairs().get(i).getCondition()),
						this.getBackendBoolExpression(boolExpr.getCondBoolExprPairs().get(i).getBoolExpr()), lastITE);
			}

			return lastITE;
		} catch (Z3Exception e) {
			String message = "could not prepare boolean if-then-else expression \"" + boolExpr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public ArithExpr prepareBoolExprAsExpr(BoolExpression boolExpr) {
		try {
			return (ArithExpr) this.context.mkITE(this.getBackendBoolExpression(boolExpr),
					this.context.mkInt(1), this.context.mkInt(0));
		} catch (Z3Exception e) {
			String message = "could not prepare boolean expression \"" + boolExpr + "\" of type \"" + boolExpr.getClass().getSimpleName() + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/** overridden expression methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public ArithExpr prepareAtomExpr(AtomExpr<?> expr) {
		try {
			if (!expr.isVariable() && !expr.getPreFieldList().isVariable()) {
				if (expr instanceof AtomBooleanExpr)
					return this.context.mkInt(((AtomBooleanExpr) expr).getValue() ? 1 : 0);
				else if (expr instanceof AtomIntegerExpr)
					return this.context.mkInt(((AtomIntegerExpr) expr).getValue());
				else if (expr instanceof AtomFloatExpr)
					return this.context.mkReal(((AtomFloatExpr) expr).getValue().toString());
				else if (expr instanceof AtomDoubleExpr)
					return this.context.mkReal(((AtomDoubleExpr) expr).getValue().toString());
				else if (expr instanceof AtomCharacterExpr)
					return this.context.mkInt(((AtomCharacterExpr) expr).getValue());
				else {
					String message = "could not create arithmetic expression from non-variable atomar expression \"" + expr + "\" with value \"" + expr.getValue() + "\" of type \"" + expr.getClass().getSimpleName() + "\"";
					Logger.getLogger(SMTIIJava.class).fatal(message);
					throw new DialectException(message);
				}
			} else {
				if (expr instanceof AtomBooleanExpr) {
					this.addAtomBooleanExpr(expr.getName());
					return this.context.mkIntConst(expr.getName());
				} else if (expr instanceof AtomIntegerExpr)
					return this.context.mkIntConst(expr.getName());
				else if (expr instanceof AtomFloatExpr)
					return this.context.mkRealConst(expr.getName());
				else if (expr instanceof AtomDoubleExpr)
					return this.context.mkRealConst(expr.getName());
				else if (expr instanceof AtomCharacterExpr) {
					this.addAtomCharacterExpr(expr.getName());
					return this.context.mkIntConst(expr.getName());
				} else if (expr instanceof AtomEnumExpr)
					return this.context.mkIntConst(expr.getName());
				else if (expr instanceof AtomObjectExpr)
					return this.context.mkIntConst(expr.getName());
				else {
					String message = "could not create arithmetic expression from variable atomar expression \"" + expr + "\"";
					Logger.getLogger(SMTIIJava.class).fatal(message);
					throw new DialectException(message);
				}
			}
		} catch (Z3Exception e) {
			String message = "could not prepare atomar expression \"" + expr + "\" of type \"" + expr.getClass().getSimpleName() + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public ArithExpr prepareArithmeticExpr(ArithmeticExpr expr) {
		try {
			switch (expr.getOperator()) {
			case ADD:
				return this.context.mkAdd(new ArithExpr[] {
						this.getBackendExpression(expr.getExpr1()),
						this.getBackendExpression(expr.getExpr2())
				});
			case SUB:
				return this.context.mkSub(new ArithExpr[] {
						this.getBackendExpression(expr.getExpr1()),
						this.getBackendExpression(expr.getExpr2())
				});
			case MUL:
				return this.context.mkMul(new ArithExpr[] {
						this.getBackendExpression(expr.getExpr1()),
						this.getBackendExpression(expr.getExpr2())
				});
			case DIV:
				return this.context.mkDiv(
						this.getBackendExpression(expr.getExpr1()),
						this.getBackendExpression(expr.getExpr2()));
			default:
				String message = "arithmetic operator \"" + expr.getOperator().getAsciiName() + "\" is not known";
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new DialectException(message);
			}
		} catch (Z3Exception e) {
			String message = "could not prepare arithmetic expression \"" + expr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public ArithExpr prepareIfThenElseExpr(IfThenElseExpr expr) {
		try {
			ArithExpr lastITE = this.getBackendExpression(expr.getElseCaseExpr());
			for (int i=expr.getCondExprPairs().size()-1; i>=0; i--) {
				lastITE = (ArithExpr) this.context.mkITE(
						this.getBackendBoolExpression(expr.getCondExprPairs().get(i).getCondition()),
						this.getBackendExpression(expr.getCondExprPairs().get(i).getExpr()), lastITE);
			}

			return lastITE;
		} catch (Z3Exception e) {
			String message = "could not prepare if-then-else expression \"" + expr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public ArithExpr preparePremAccessibleObjectExpr(PremAccessibleObjectExpr<?> expr) {
		try {
			if (expr instanceof PremMethodExpr) {
				Method method = ((PremMethodExpr) expr).getAccessibleObject();
				ArithExpr arithExpr = this.getBackendExpression(expr.getExpr());
	
				if (this.isIntegerValueMethod(method)) {
					if (arithExpr instanceof RealExpr)
						/** expr >= 0 ? to_int expr : - to_int (- expr) */
						return (ArithExpr) this.context.mkITE(
								this.context.mkGe(arithExpr, this.context.mkReal(0)),
								this.context.mkReal2Int((RealExpr) arithExpr),
								this.context.mkSub(this.context.mkReal(0), this.context.mkReal2Int((RealExpr) this.context.mkSub(this.context.mkReal(0), arithExpr))));
					else if (arithExpr instanceof IntExpr)
						return arithExpr;
					else {
						String message = "can not get int value from arithmetic expression other than int or real";
						Logger.getLogger(SMTIIJava.class).fatal(message);
						throw new DialectException(message);
					}
				} else if (this.isFloatValueMethod(method) || this.isDoubleValueMethod(method)) {
					if (arithExpr instanceof RealExpr)
						return arithExpr;
					else if (arithExpr instanceof IntExpr)
						return this.context.mkInt2Real((IntExpr) arithExpr);
					else {
						String message = "can not get real value from arithmetic expression other than int or real";
						Logger.getLogger(SMTIIJava.class).fatal(message);
						throw new DialectException(message);
					}
				} else {
					String message = "preparable method with name \"" + method.getName() + "\" is not supported";
					Logger.getLogger(SMTIIJava.class).fatal(message);
					throw new DialectException(message);
				}
			} else {
				String message = "accessible object \"" + expr.getAccessibleObject() + "\" of type \"" + expr.getClass().getSimpleName() + "\" is not preparable";
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new DialectException(message);
			}
		} catch (Z3Exception e) {
			String message = "could not prepare premature accessible object expression \"" + expr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	@Override
	public ArithExpr preparePremClasscastExpr(PremClasscastExpr expr) {
		try {
			String message;
			switch (expr.getKeyword()) {
			case f2d:
				if (expr.getExpr() instanceof AtomFloatExpr)
					return this.getBackendExpression(expr);
				else
					message = "can not cast non-float type \"" + expr.getExpr() + "\" to real";
			case i2f:
			case i2d:
				if (expr.getExpr() instanceof AtomIntegerExpr)
					return this.context.mkInt2Real((IntExpr) this.getBackendExpression(expr.getExpr()));
				else
					message = "can not cast non-integer type \"" + expr.getExpr() + "\" to real";
				break;
			default:
				message = "undefined casting \"" + expr.getKeyword() + "\" for expressions";
				break;
			}

			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		} catch (Z3Exception e) {
			String message = "could not prepare premature classcast expression \"" + expr + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr
	 */
	private void addAtomBooleanExpr(String expr) {
		if (!this.atomBooleanExprSet.contains(expr)) {
			this.atomBooleanExprSet.add(expr);
			this.curBoolExprs.add(this.getBackendBoolExpression(
					new ConnectedBoolExpr(
							BooleanConnector.OR,
							new CompareExpr(new AtomIntegerExpr(expr), CompareOperator.EQUAL, new AtomIntegerExpr(0)),
							new CompareExpr(new AtomIntegerExpr(expr), CompareOperator.EQUAL, new AtomIntegerExpr(1)))));
		}
	}

	/**
	 * COMMENT TODO probably no lower boundary?
	 * 
	 * @param expr
	 */
	private void addAtomCharacterExpr(String expr) {
		if (!this.atomCharacterExprSet.contains(expr)) {
			this.atomCharacterExprSet.add(expr);
			this.curBoolExprs.add(this.getBackendBoolExpression(
					new ConnectedBoolExpr(
							BooleanConnector.AND,
							new CompareExpr(new AtomIntegerExpr(expr), CompareOperator.GREATER_EQUAL, new AtomIntegerExpr(-1)),
							new CompareExpr(new AtomIntegerExpr(expr), CompareOperator.LESS, new AtomIntegerExpr(1 << 16)))));
		}
	}
}
