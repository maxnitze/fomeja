package de.agra.sat.koselleck.backends;

/** imports */
import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.RatNum;
import com.microsoft.z3.Z3Exception;

import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractNotConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralDouble;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralFloat;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralString;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;
import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.utils.CompareUtils;

/**
 * 
 * @author Max Nitze
 */
public class SMTIIJava extends Dialect<BoolExpr, ArithExpr> {
	/**  */
	private Context context;

	/**
	 * 
	 */
	public SMTIIJava() {
		super(Type.smt2);

		try {
			this.context = new Context(new HashMap<String, String>());
		} catch (Z3Exception e) {
			String message = "could not instantiate SMTIIJava due to z3 exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new RuntimeException(message);
		}
	}

	/**
	 * 
	 * @return
	 */
	public Context getContext() {
		return this.context;
	}

	@Override
	public BoolExpr format(Theorem theorem) throws NotSatisfiableException {
		BoolExpr[] booleanExpressions = new BoolExpr[theorem.constraintsSize];
		for (int i = 0; i < theorem.constraintsSize; i++)
			booleanExpressions[i] = this.getBackendConstraint(theorem.abstractConstraints.get(i));

		try {
			return this.context.MkAnd(booleanExpressions);
		} catch (Z3Exception e) {
			String message = "could not prepare all constraints";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public Map<String, Object> parseResult(Object resultObject) {
		if (resultObject instanceof Model) {
			Model model = (Model) resultObject;

			Map<String, Object> resultMap = new HashMap<String, Object>();

			try {
				for (FuncDecl constDecl : model.ConstDecls()) {
					Expr resultExpression = model.ConstInterp(constDecl);
					if (resultExpression.IsReal()) {
						RatNum rationalNumber = (RatNum) resultExpression;
						resultMap.put(constDecl.Name().toString(), new Double(rationalNumber.Numerator().Int() / rationalNumber.Denominator().Int()));
					} else if (resultExpression.IsInt())
						resultMap.put(constDecl.Name().toString(), ((IntNum) resultExpression).Int());
				}
			} catch (Z3Exception e) {
				String message = "could not get constant declarations from result model";
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new IllegalArgumentException(message);
			}

			return resultMap;
		} else {
			String message = "could not parse result of type \"" + resultObject.getClass().getCanonicalName() + "\"; only String supported";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractBooleanConstraint(AbstractBooleanConstraint booleanConstraint) {
		try {
			return this.context.MkBool(booleanConstraint.value);
		} catch (Z3Exception e) {
			String message = "could not make boolean expression from boolean constraint \"" + booleanConstraint + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractNotConstraint(AbstractNotConstraint notConstraint) {
		try {
			return this.context.MkNot(this.getBackendConstraint(notConstraint.constraint));
		} catch (Z3Exception e) {
			String message = "could not negotiate boolean expression \"" + notConstraint + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractSingleConstraint(AbstractSingleConstraint singleConstraint) {
		try {
			switch (singleConstraint.operator) {
			case EQUAL:
				return this.context.MkEq(this.getBackendConstraintValue(singleConstraint.value1), this.getBackendConstraintValue(singleConstraint.value2));
			case GREATER:
				return this.context.MkGt(this.getBackendConstraintValue(singleConstraint.value1), this.getBackendConstraintValue(singleConstraint.value2));
			case GREATER_EQUAL:
				return this.context.MkGe(this.getBackendConstraintValue(singleConstraint.value1), this.getBackendConstraintValue(singleConstraint.value2));
			case LESS:
				return this.context.MkLt(this.getBackendConstraintValue(singleConstraint.value1), this.getBackendConstraintValue(singleConstraint.value2));
			case LESS_EQUAL:
				return this.context.MkLe(this.getBackendConstraintValue(singleConstraint.value1), this.getBackendConstraintValue(singleConstraint.value2));
			case NOT_EQUAL:
				return this.context.MkNot(this.context.MkEq(this.getBackendConstraintValue(singleConstraint.value1), this.getBackendConstraintValue(singleConstraint.value2)));
			default:
				RuntimeException exception = new UnknownConstraintOperatorException(singleConstraint.operator);
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare single constraint \"" + singleConstraint + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractSubConstraint(AbstractSubConstraint subConstraint) {
		try {
			switch (subConstraint.connector) {
			case AND:
				return this.context.MkAnd(new BoolExpr[] {
						this.getBackendConstraint(subConstraint.constraint1),
						this.getBackendConstraint(subConstraint.constraint2)
				});
			case OR:
				return this.context.MkOr(new BoolExpr[] {
						this.getBackendConstraint(subConstraint.constraint1),
						this.getBackendConstraint(subConstraint.constraint2)
				});
			default:
				RuntimeException exception = new UnknownBooleanConnectorException(subConstraint.connector);
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare single constraint \"" + subConstraint + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractIfThenElseConstraint(AbstractIfThenElseConstraint ifThenElseConstraint) {
		try {
			return this.context.MkOr(new BoolExpr[] {
					this.context.MkAnd(new BoolExpr[] {
							this.getBackendConstraint(ifThenElseConstraint.ifCondition),
							this.getBackendConstraint(ifThenElseConstraint.thenCaseConstraint)
					}),
					this.context.MkAnd(new BoolExpr[] {
							this.context.MkNot(this.getBackendConstraint(ifThenElseConstraint.ifCondition)),
							this.getBackendConstraint(ifThenElseConstraint.elseCaseConstraint)
					})
			});
		} catch (Z3Exception e) {
			String message = "could not prepare if-then-else constraint \"" + ifThenElseConstraint + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public ArithExpr prepareAbstractConstraintLiteral(AbstractConstraintLiteral<?> constraintLiteral) {
		try {
			if (constraintLiteral instanceof AbstractConstraintLiteralDouble)
				return this.context.MkReal(constraintLiteral.toString());
			else if (constraintLiteral instanceof AbstractConstraintLiteralFloat)
				return this.context.MkReal(constraintLiteral.toString());
			else if (constraintLiteral instanceof AbstractConstraintLiteralInteger)
				return this.context.MkInt(constraintLiteral.toString());
			else if (constraintLiteral instanceof AbstractConstraintLiteralString) {
				AbstractConstraintLiteralString constraintLiteralString = (AbstractConstraintLiteralString) constraintLiteral;
				if (CompareUtils.equalsAny(constraintLiteralString.type, CompareUtils.doubleClasses))
					return this.context.MkRealConst(constraintLiteralString.value);
				else if (CompareUtils.equalsAny(constraintLiteralString.type, CompareUtils.floatClasses))
					return this.context.MkRealConst(constraintLiteralString.value);
				else if (CompareUtils.equalsAny(constraintLiteralString.type, CompareUtils.integerClasses))
					return this.context.MkIntConst(constraintLiteralString.value);
				else {
					String message = "could not create arithmetic expression from literal string \"" + constraintLiteralString + "\"";
					Logger.getLogger(SMTIIJava.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			} else {
				String message = "could not create arithmetic expression from literal \"" + constraintLiteral + "\"";
				Logger.getLogger(SMTIIJava.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		} catch (Z3Exception e) {
			String message = "could not prepare constraint literal \"" + constraintLiteral + "\"\n\t" + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public ArithExpr prepareAbstractConstraintFormula(AbstractConstraintFormula constraintFormula) {
		try {
			switch (constraintFormula.operator) {
			case ADD:
				return this.context.MkAdd(new ArithExpr[] {
						this.getBackendConstraintValue(constraintFormula.value1),
						this.getBackendConstraintValue(constraintFormula.value2)
				});
			case SUB:
				return this.context.MkSub(new ArithExpr[] {
						this.getBackendConstraintValue(constraintFormula.value1),
						this.getBackendConstraintValue(constraintFormula.value2)
				});
			case MUL:
				return this.context.MkMul(new ArithExpr[] {
						this.getBackendConstraintValue(constraintFormula.value1),
						this.getBackendConstraintValue(constraintFormula.value2)
				});
			case DIV:
				return this.context.MkDiv(
						this.getBackendConstraintValue(constraintFormula.value1),
						this.getBackendConstraintValue(constraintFormula.value2));
			default:
				RuntimeException exception = new UnknownArithmeticOperatorException(constraintFormula.operator);
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare constraint formula \"" + constraintFormula + "\"";
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}
}
