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
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractNotConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraintSet;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralDouble;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralFloat;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralInteger;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;
import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class SMTIIJava extends Dialect<BoolExpr, ArithExpr> {
	/** COMMENT */
	private final Context context;

	/**
	 * COMMENT
	 */
	public SMTIIJava() {
		super(Type.smt2);

		try {
			this.context = new Context(new HashMap<String, String>());
		} catch (Z3Exception e) {
			String message = "could not instantiate SMTIIJava due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new RuntimeException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Context getContext() {
		return this.context;
	}

	@Override
	public BoolExpr format(Theorem theorem) throws NotSatisfiableException {
		BoolExpr[] booleanExpressions = new BoolExpr[theorem.getConstraintSize()];
		for (int i=0; i<theorem.getConstraintSize(); i++)
			booleanExpressions[i] = this.getBackendConstraint(theorem.getAbstractConstraint().get(i));

		try {
			return this.context.MkAnd(booleanExpressions);
		} catch (Z3Exception e) {
			String message = "could not prepare all constraints due to exception: " + e.getMessage();
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
			return this.context.MkBool(booleanConstraint.getValue());
		} catch (Z3Exception e) {
			String message = "could not make boolean expression from boolean constraint \"" + booleanConstraint + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractNotConstraint(AbstractNotConstraint notConstraint) {
		try {
			return this.context.MkNot(this.getBackendConstraint(notConstraint.getConstraint()));
		} catch (Z3Exception e) {
			String message = "could not negotiate boolean expression \"" + notConstraint + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractSingleConstraint(AbstractSingleConstraint singleConstraint) {
		try {
			switch (singleConstraint.getOperator()) {
			case EQUAL:
				return this.context.MkEq(this.getBackendConstraintValue(singleConstraint.getValue1()), this.getBackendConstraintValue(singleConstraint.getValue2()));
			case GREATER:
				return this.context.MkGt(this.getBackendConstraintValue(singleConstraint.getValue1()), this.getBackendConstraintValue(singleConstraint.getValue2()));
			case GREATER_EQUAL:
				return this.context.MkGe(this.getBackendConstraintValue(singleConstraint.getValue1()), this.getBackendConstraintValue(singleConstraint.getValue2()));
			case LESS:
				return this.context.MkLt(this.getBackendConstraintValue(singleConstraint.getValue1()), this.getBackendConstraintValue(singleConstraint.getValue2()));
			case LESS_EQUAL:
				return this.context.MkLe(this.getBackendConstraintValue(singleConstraint.getValue1()), this.getBackendConstraintValue(singleConstraint.getValue2()));
			case NOT_EQUAL:
				return this.context.MkNot(this.context.MkEq(this.getBackendConstraintValue(singleConstraint.getValue1()), this.getBackendConstraintValue(singleConstraint.getValue2())));
			default:
				RuntimeException exception = new UnknownConstraintOperatorException(singleConstraint.getOperator());
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare single constraint \"" + singleConstraint + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractSubConstraint(AbstractSubConstraint subConstraint) {
		try {
			switch (subConstraint.getConnector()) {
			case AND:
				return this.context.MkAnd(new BoolExpr[] {
						this.getBackendConstraint(subConstraint.getConstraint1()),
						this.getBackendConstraint(subConstraint.getConstraint2())
				});
			case OR:
				return this.context.MkOr(new BoolExpr[] {
						this.getBackendConstraint(subConstraint.getConstraint1()),
						this.getBackendConstraint(subConstraint.getConstraint2())
				});
			default:
				RuntimeException exception = new UnknownBooleanConnectorException(subConstraint.getConnector());
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare single constraint \"" + subConstraint + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractSubConstraintSet(AbstractSubConstraintSet subConstraintSet) {
		BoolExpr[] boolExprs = new BoolExpr[subConstraintSet.getConstraints().size()];
		int i = 0;
		for (AbstractConstraint constraint : subConstraintSet.getConstraints())
			boolExprs[i++] = this.getBackendConstraint(constraint);
		try {
			switch (subConstraintSet.getConnector()) {
			case AND:
				return this.context.MkAnd(boolExprs);
			case OR:
				return this.context.MkOr(boolExprs);
			default:
				RuntimeException exception = new UnknownBooleanConnectorException(subConstraintSet.getConnector());
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare single constraint \"" + subConstraintSet + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public BoolExpr prepareAbstractIfThenElseConstraint(AbstractIfThenElseConstraint ifThenElseConstraint) {
		try {
			return this.context.MkOr(new BoolExpr[] {
					this.context.MkAnd(new BoolExpr[] {
							this.getBackendConstraint(ifThenElseConstraint.getIfCondition()),
							this.getBackendConstraint(ifThenElseConstraint.getThenCaseConstraint())
					}),
					this.context.MkAnd(new BoolExpr[] {
							this.context.MkNot(this.getBackendConstraint(ifThenElseConstraint.getIfCondition())),
							this.getBackendConstraint(ifThenElseConstraint.getElseCaseConstraint())
					})
			});
		} catch (Z3Exception e) {
			String message = "could not prepare if-then-else constraint \"" + ifThenElseConstraint + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public ArithExpr prepareAbstractConstraintLiteral(AbstractConstraintLiteral<?> constraintLiteral) {
		try {
			if (!constraintLiteral.isVariable()) {
				if (constraintLiteral instanceof AbstractConstraintLiteralDouble)
					return this.context.MkReal(constraintLiteral.getValue().toString());
				else if (constraintLiteral instanceof AbstractConstraintLiteralFloat)
					return this.context.MkReal(constraintLiteral.getValue().toString());
				else if (constraintLiteral instanceof AbstractConstraintLiteralInteger)
					return this.context.MkInt(constraintLiteral.getValue().toString());
				else {
					String message = "could not create arithmetic expression from non-variable literal \"" + constraintLiteral + "\"";
					Logger.getLogger(SMTIIJava.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			} else {
				if (constraintLiteral instanceof AbstractConstraintLiteralDouble)
					return this.context.MkRealConst(constraintLiteral.getName());
				else if (constraintLiteral instanceof AbstractConstraintLiteralFloat)
					return this.context.MkRealConst(constraintLiteral.getName());
				else if (constraintLiteral instanceof AbstractConstraintLiteralInteger)
					return this.context.MkIntConst(constraintLiteral.getName());
				else if (constraintLiteral instanceof AbstractConstraintLiteralObject)
					return this.context.MkIntConst(constraintLiteral.getName());
				else {
					String message = "could not create arithmetic expression from variable literal \"" + constraintLiteral + "\"";
					Logger.getLogger(SMTIIJava.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			}
		} catch (Z3Exception e) {
			String message = "could not prepare constraint literal \"" + constraintLiteral + "\" of type \"" + constraintLiteral.getClass().getSimpleName() + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	@Override
	public ArithExpr prepareAbstractConstraintFormula(AbstractConstraintFormula constraintFormula) {
		try {
			switch (constraintFormula.getOperator()) {
			case ADD:
				return this.context.MkAdd(new ArithExpr[] {
						this.getBackendConstraintValue(constraintFormula.getValue1()),
						this.getBackendConstraintValue(constraintFormula.getValue2())
				});
			case SUB:
				return this.context.MkSub(new ArithExpr[] {
						this.getBackendConstraintValue(constraintFormula.getValue1()),
						this.getBackendConstraintValue(constraintFormula.getValue2())
				});
			case MUL:
				return this.context.MkMul(new ArithExpr[] {
						this.getBackendConstraintValue(constraintFormula.getValue1()),
						this.getBackendConstraintValue(constraintFormula.getValue2())
				});
			case DIV:
				return this.context.MkDiv(
						this.getBackendConstraintValue(constraintFormula.getValue1()),
						this.getBackendConstraintValue(constraintFormula.getValue2()));
			default:
				RuntimeException exception = new UnknownArithmeticOperatorException(constraintFormula.getOperator());
				Logger.getLogger(SMTIIJava.class).fatal(exception.getMessage());
				throw exception;
			}
		} catch (Z3Exception e) {
			String message = "could not prepare constraint formula \"" + constraintFormula + "\" due to exception: " + e.getMessage();
			Logger.getLogger(SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}
}
