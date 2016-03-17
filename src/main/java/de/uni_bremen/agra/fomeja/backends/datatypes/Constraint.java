package de.uni_bremen.agra.fomeja.backends.datatypes;

/* imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_bremen.agra.fomeja.backends.parameterobjects.ParameterObject;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremStmtSeqExpr;
import de.uni_bremen.agra.fomeja.decompiling.misc.ComponentVariables;
import de.uni_bremen.agra.fomeja.decompiling.statements.StatementSeq;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Constraint {
	/** COMMENT */
	private List<SingleConstraint> singleConstraints;

	/** COMMENT */
	private List<BoolExpression> constraintExprs;
	/** COMMENT */
	private Set<ParameterObject> parameterObjects;

	/**
	 * COMMENT
	 */
	public Constraint() {
		this.singleConstraints = new ArrayList<SingleConstraint>();
		this.constraintExprs = new ArrayList<BoolExpression>();
		this.parameterObjects = new HashSet<ParameterObject>();
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public List<BoolExpression> getConstraintExprs() {
		return this.constraintExprs;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Set<ParameterObject> getParameterObjects() {
		return this.parameterObjects;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getConstraintSize() {
		return this.constraintExprs.size();
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param stmtSeq COMMENT
	 * @param fields COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean addSingleConstraint(StatementSeq stmtSeq, List<Field>[] fields) {
		return this.singleConstraints.add(new SingleConstraint(stmtSeq, fields));
	}

	/**
	 * COMMENT
	 * 
	 * @param component COMMENT
	 */
	public void unfoldConstraints(Object component) {
		this.constraintExprs.clear();
		this.parameterObjects.clear();

		List<BoolExpression> constraintExprs = new ArrayList<BoolExpression>();

		ComponentVariables compVars = new ComponentVariables(component);

		for (SingleConstraint singleConstraint : this.singleConstraints) {
			ConstraintParameterList constraintParameterList = new ConstraintParameterList(singleConstraint.fields.length);
			for (int i=0; i<singleConstraint.fields.length; i++)
				constraintParameterList.add(i, component, singleConstraint.fields[i]);

			/** skip if constraint has parameters, but none to invoke it with */
			if (constraintParameterList.size() != 0 && !constraintParameterList.isIncrementable())
				continue;

			do {
				StatementSeq clonedStmtSeq = singleConstraint.stmtSeq.clone();

				Map<String, Expression> params = new HashMap<String, Expression>();
				for (int i=0; i<constraintParameterList.size(); i++)
					params.put("store" + clonedStmtSeq.getStoreIndex() + "_" + (i+1), new AtomObjectExpr(constraintParameterList.get(i).getCurrentCollectionObject()));
				clonedStmtSeq.substitudeParams(params);

				BoolExpression boolExpr =
						new CompareExpr(new PremStmtSeqExpr(clonedStmtSeq), CompareOperator.EQUAL, new AtomIntegerExpr(1));

				constraintExprs.add(boolExpr.evaluate(compVars));
			} while (constraintParameterList.increment());
		}

		this.parameterObjects.addAll(compVars.getParameterObjects());

		this.constraintExprs.addAll(compVars.getRangeExprs());
		this.constraintExprs.addAll(compVars.getConnectionExprs());
		this.constraintExprs.addAll(constraintExprs);
	}

	/** private classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @version 1.0.0
	 * @author Max Nitze
	 */
	private class SingleConstraint {
		/** the boolean expression of the theorem */
		private final StatementSeq stmtSeq;
		/** array of lists where each list describes the collections to iterate
		 * over the constraint parameters at the index of the list */
		private final List<Field>[] fields;

		/**
		 * Constructor for a new abstract single theorem.
		 * 
		 * @param stmtSeq the new statement sequence
		 * @param fields the new field list array
		 */
		public SingleConstraint(StatementSeq stmtSeq, List<Field>[] fields) {
			this.stmtSeq = stmtSeq;
			this.fields = fields;
		}
	}
}
