package de.uni_bremen.agra.fomeja.testutils;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomBooleanExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomClassExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomEnumExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.NotExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArrayelementExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArraylengthExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremConstructorExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremFieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremGetfieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremLoopStmtExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremStmtSeqExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PrematureExpr;
import de.uni_bremen.agra.fomeja.testutils.exceptions.RandElementGeneratorException;
import de.uni_bremen.agra.fomeja.types.ArithmeticOperator;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;
import de.uni_bremen.agra.fomeja.types.CompareOperator;
import de.uni_bremen.agra.fomeja.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class RandElementGenerator {
	/** COMMENT */
	private static final Random RANDOMIZER;

	/** COMMENT */
	private static final List<Class<?>> CLASSES;
	/** COMMENT */
	private static final List<Class<? extends Enum<?>>> ENUM_CLASSES;

	/** COMMENT */
	private static final int MAX_DEPTH;

	/** COMMENT */
	private static final int MAX_STRING_LENGTH;
	/** COMMENT */
	private static final int MAX_CHARACTER;
	/** COMMENT */
	private static final int MAX_LIST_SIZE;

	/* COMMENT */
	static {
		RANDOMIZER = new Random();

		CLASSES = new ArrayList<Class<?>>();
		CLASSES.add(Boolean.class);
		CLASSES.add(Character.class);
		CLASSES.add(Double.class);
		CLASSES.add(Float.class);
		CLASSES.add(Integer.class);

		ENUM_CLASSES = new ArrayList<Class<? extends Enum<?>>>();
		ENUM_CLASSES.add(Opcode.class);
		ENUM_CLASSES.add(ArithmeticOperator.class);
		ENUM_CLASSES.add(CompareOperator.class);
		ENUM_CLASSES.add(BooleanConnector.class);
		ENUM_CLASSES.add(ExprClass.class);
		ENUM_CLASSES.add(BoolExprClass.class);
		ENUM_CLASSES.add(AtomExprClass.class);

		MAX_DEPTH = 1<<3;

		MAX_STRING_LENGTH = 32;
		MAX_CHARACTER = 1<<16;
		MAX_LIST_SIZE = 16;
	}

	/* generator methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param exprClass COMMENT
	 * 
	 * @return COMMENT
	 */
	public static <T extends Expression> T generateExpr(Class<T> exprClass) {
		return generateExpr(exprClass, false, MAX_DEPTH);
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExprClass COMMENT
	 * 
	 * @return COMMENT
	 */
	public static <T extends BoolExpression> T generateBoolExpr(Class<T> boolExprClass) {
		return generateBoolExpr(boolExprClass, MAX_DEPTH);
	}

	/* private generator classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param exprClass COMMENT
	 * @param returnNumber COMMENT
	 * @param depth COMMENT
	 * 
	 * @return COMMENT
	 */
	@SuppressWarnings("unchecked")
	private static <T extends Expression> T generateExpr(Class<T> exprClass, boolean returnNumber, int depth) {
		int newDepth = depth-1;
		switch (ExprClass.valueOf(exprClass)) {
		/* general expression classes */
		case ArithmeticExpr:
			return (T) new ArithmeticExpr(
					generateExpr(ExprClass.getRandom(true, newDepth).cls, true, newDepth),
					ArithmeticOperator.values()[RANDOMIZER.nextInt(ArithmeticOperator.values().length)],
					generateExpr(ExprClass.getRandom(true, newDepth).cls, true, newDepth));
		case IfThenElseExpr:
			return (T) new IfThenElseExpr(
					generateBoolExpr(BoolExprClass.getRandom(newDepth).cls, newDepth),
					generateExpr(ExprClass.getRandom(returnNumber, newDepth).cls, returnNumber, newDepth),
					generateExpr(ExprClass.getRandom(returnNumber, newDepth).cls, returnNumber, newDepth));
		/* atomar expression classes */
		case AtomExpr:
			return (T) generateAtomExpr(AtomExprClass.getRandom(returnNumber, depth).cls, returnNumber, depth);
		/* boolean expression classes */
		case BoolExpression:
			return (T) generateBoolExpr(BoolExprClass.getRandom(depth).cls, depth);
		/* default case */
		default:
			String message = "can not process unknown expression class type \"" + exprClass + "\"";
			Logger.getLogger(RandElementGenerator.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExprClass COMMENT
	 * @param depth COMMENT
	 * 
	 * @return COMMENT
	 */
	@SuppressWarnings("unchecked")
	private static <T extends BoolExpression> T generateBoolExpr(Class<T> boolExprClass, int depth) {
		int newDepth = depth-1;
		switch (BoolExprClass.valueOf(boolExprClass)) {
		/* boolean expression classes */
		case AtomBoolExpr:
			return (T) new AtomBoolExpr(RANDOMIZER.nextBoolean());
		case BoolIfThenElseExpr:
			BoolIfThenElseExpr boolIfThenElseExpr = new BoolIfThenElseExpr(
					generateBoolExpr(BoolExprClass.getRandom(newDepth).cls, newDepth));
			int condExprPairSize = RANDOMIZER.nextInt(MAX_LIST_SIZE);
			for (int i=0; i<condExprPairSize; i++)
				boolIfThenElseExpr.add(
						generateBoolExpr(BoolExprClass.getRandom(newDepth).cls, newDepth),
						generateBoolExpr(BoolExprClass.getRandom(newDepth).cls, newDepth));
			return (T) boolIfThenElseExpr;
		case CompareExpr:
			return (T) new CompareExpr(
					generateExpr(ExprClass.getRandom(true, newDepth).cls, true, newDepth),
					CompareOperator.values()[RANDOMIZER.nextInt(CompareOperator.values().length)],
					generateExpr(ExprClass.getRandom(true, newDepth).cls, true, newDepth));
		case ConnectedBoolExpr:
			ConnectedBoolExpr connectedBoolExpr = new ConnectedBoolExpr(
					BooleanConnector.values()[RANDOMIZER.nextInt(BooleanConnector.values().length)]);
			int connectedExprPairSize = RANDOMIZER.nextInt(MAX_LIST_SIZE);
			for (int i=0; i<connectedExprPairSize; i++)
				connectedBoolExpr.add(generateBoolExpr(BoolExprClass.getRandom(newDepth).cls, newDepth));
			return (T) connectedBoolExpr;
		case NotExpr:
			return (T) new NotExpr(generateBoolExpr(BoolExprClass.getRandom(newDepth).cls, newDepth));
		/* default case */
		default:
			String message = "can not process unknown bool expression class type \"" + boolExprClass + "\"";
			Logger.getLogger(RandElementGenerator.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExprClass COMMENT
	 * @param returnNumber COMMENT
	 * @param depth COMMENT
	 * 
	 * @return COMMENT
	 */
	@SuppressWarnings("unchecked")
	private static <T extends AtomExpr<?>> T generateAtomExpr(Class<T> atomExprClass, boolean returnNumber, int depth) {
		switch(AtomExprClass.valueOf(atomExprClass)) {
		/* atomar expression classes */
//		case AtomArrayExpr:
//			return (T) null;
		case AtomBooleanExpr:
			return (T) generateAtomExprForClass(Boolean.class);
		case AtomCharacterExpr:
			return (T) generateAtomExprForClass(Character.class);
		case AtomClassExpr:
			return (T) new AtomClassExpr(CLASSES.get(RANDOMIZER.nextInt(CLASSES.size())));
		case AtomDoubleExpr:
			return (T) generateAtomExprForClass(Double.class);
		case AtomEnumExpr:
			return (T) generateAtomExprForClass(ENUM_CLASSES.get(RANDOMIZER.nextInt(ENUM_CLASSES.size())));
		case AtomFloatExpr:
			return (T) generateAtomExprForClass(Float.class);
		case AtomIntegerExpr:
			return (T) generateAtomExprForClass(Integer.class);
		case AtomObjectExpr:
			return (T) generateAtomExprForClass(Object.class);
		case AtomStringExpr:
			return (T) generateAtomExprForClass(String.class);
		case AtomVoidExpr:
			return (T) new AtomVoidExpr();
		/* default case */
		default:
			String message = "can not process unknown atomar expression class type \"" + atomExprClass + "\"";
			Logger.getLogger(RandElementGenerator.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param cls COMMENT
	 * 
	 * @return COMMENT
	 */
	private static AtomExpr<?> generateAtomExprForClass(Class<?> cls) {
		if (cls.equals(Boolean.class))
			return new AtomBooleanExpr(RANDOMIZER.nextBoolean());
		else if (cls.equals(Character.class))
			return new AtomCharacterExpr((char) RANDOMIZER.nextInt(MAX_CHARACTER));
		else if (cls.equals(Double.class))
			return new AtomDoubleExpr(RANDOMIZER.nextDouble());
		else if (cls.equals(Float.class))
			return new AtomFloatExpr(RANDOMIZER.nextFloat());
		else if (cls.equals(Integer.class))
			return new AtomIntegerExpr(RANDOMIZER.nextInt());
		else if (cls.equals(String.class)) {
			int stringLength = RANDOMIZER.nextInt(MAX_STRING_LENGTH);
			StringBuilder stringBuilder = new StringBuilder();
			for (int i=0; i<stringLength; i++)
				stringBuilder.append((char) RANDOMIZER.nextInt(MAX_CHARACTER));
			return new AtomStringExpr(stringBuilder.toString());
		} else if (cls.isEnum())
			return new AtomEnumExpr((Enum<?>) cls.getEnumConstants()[RANDOMIZER.nextInt(cls.getEnumConstants().length)]);
		else
			return new AtomObjectExpr(new Object());
	}

	/* private inner classes
	 * ----- ----- ----- ----- ----- */

	/** COMMENT */
	private static enum Attr {
		GENERAL,
		ATOMAR,
		BOOL,
		MISC,
		PREMATURE,

		CAN_RETURN_NUMBER,
		IS_FINAL;

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public int bit() {
			return 1<<this.ordinal();
		}
	};

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static enum ExprClass {
		/* expression classes */
		ArithmeticExpr(ArithmeticExpr.class,
				Attr.GENERAL.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		IfThenElseExpr(IfThenElseExpr.class,
				Attr.GENERAL.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		/* atomar expression classes */
		AtomExpr(AtomExpr.class,
				Attr.ATOMAR.bit() | Attr.CAN_RETURN_NUMBER.bit() | Attr.IS_FINAL.bit()),
		/* bool expression classes */
		BoolExpression(BoolExpression.class,
				Attr.BOOL.bit() | Attr.IS_FINAL.bit());

		/** COMMENT */
		private Class<? extends Expression> cls;
		/** COMMENT */
		private int typeMap;

		/**
		 * COMMENT
		 * 
		 * @param cls COMMENT
		 * @param typeMap COMMENT
		 * @param canResultInNumber COMMENT
		 */
		ExprClass(Class<? extends Expression> cls, int typeMap) {
			this.cls = cls;
			this.typeMap = typeMap;
		}

		/* value methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param exprClass COMMENT
		 * 
		 * @return COMMENT
		 */
		public static ExprClass valueOf(Class<? extends Expression> exprClass) {
			for (ExprClass value : values())
				if (value.cls.equals(exprClass))
					return value;
	
			String message = "can not get expression class for class \"" + exprClass.getSimpleName() + "\"";
			Logger.getLogger(ExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}

		/* random getter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param returnNumber COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		public static ExprClass getRandom(boolean returnNumber, int depth) {
			return getTypedExprClass(0 | (returnNumber ? Attr.CAN_RETURN_NUMBER.bit() : 0), depth);
		}

		/**
		 * COMMENT
		 * 
		 * @param typeMap COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		private static ExprClass getTypedExprClass(int typeMap, int depth) {
			if (depth == 0)
				typeMap |= Attr.IS_FINAL.bit();

			if (typeMap == 0)
				return values()[RANDOMIZER.nextInt(values().length)];

			int typeMapCount = 0;
			for (ExprClass exprClass : values())
				if ((exprClass.typeMap & typeMap) == typeMap)
					++typeMapCount;

			int rand = RANDOMIZER.nextInt(typeMapCount);
			for (ExprClass exprClass : values()) {
				if ((exprClass.typeMap & typeMap) == typeMap) {
					if (rand == 0)
						return exprClass;
					else
						--rand;
				}
			}

			String message = "generated random value greater than the amount of available classes!";
			Logger.getLogger(ExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	};

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static enum BoolExprClass {
		/* bool expression classes */
		AtomBoolExpr(AtomBoolExpr.class,
				Attr.BOOL.bit() | Attr.IS_FINAL.bit()),
		BoolIfThenElseExpr(BoolIfThenElseExpr.class,
				Attr.BOOL.bit()),
		CompareExpr(CompareExpr.class,
				Attr.BOOL.bit()),
		ConnectedBoolExpr(ConnectedBoolExpr.class,
				Attr.BOOL.bit()),
		NotExpr(NotExpr.class,
				Attr.BOOL.bit());

		/** COMMENT */
		private Class<? extends BoolExpression> cls;
		/** COMMENT */
		private int typeMap;

		/**
		 * COMMENT
		 * 
		 * @param cls COMMENT
		 * @param typeMap COMMENT
		 */
		BoolExprClass(Class<? extends BoolExpression> cls, int typeMap) {
			this.cls = cls;
			this.typeMap = typeMap;
		}

		/* value methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param exprClass COMMENT
		 * 
		 * @return COMMENT
		 */
		public static BoolExprClass valueOf(Class<? extends BoolExpression> exprClass) {
			for (BoolExprClass value : values())
				if (value.cls.equals(exprClass))
					return value;
	
			String message = "can not get expression class for class \"" + exprClass.getSimpleName() + "\"";
			Logger.getLogger(BoolExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}

		/* random getter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		public static BoolExprClass getRandom(int depth) {
			return getTypedExprClass(0, depth);
		}

		/**
		 * COMMENT
		 * 
		 * @param typeMap COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		private static BoolExprClass getTypedExprClass(int typeMap, int depth) {
			if (depth == 0)
				typeMap |= Attr.IS_FINAL.bit();

			if (typeMap == 0)
				return values()[RANDOMIZER.nextInt(values().length)];

			int typeMapCount = 0;
			for (BoolExprClass boolExprClass : values())
				if ((boolExprClass.typeMap & typeMap) == typeMap)
					++typeMapCount;

			int rand = RANDOMIZER.nextInt(typeMapCount);
			for (BoolExprClass boolExprClass : values()) {
				if ((boolExprClass.typeMap & typeMap) == typeMap) {
					if (rand == 0)
						return boolExprClass;
					else
						--rand;
				}
			}

			String message = "generated random value greater than the amount of available classes!";
			Logger.getLogger(BoolExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	};

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static enum AtomExprClass {
		/* atomar expression classes */
//		AtomArrayExpr(AtomArrayExpr.class,
//				Attr.ATOMAR.bit()),
		AtomBooleanExpr(AtomBooleanExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit()),
		AtomCharacterExpr(AtomCharacterExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit()),
		AtomClassExpr(AtomClassExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit()),
		AtomDoubleExpr(AtomDoubleExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		AtomEnumExpr(AtomEnumExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit()),
		AtomFloatExpr(AtomFloatExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		AtomIntegerExpr(AtomIntegerExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		AtomObjectExpr(AtomObjectExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit()),
		AtomStringExpr(AtomStringExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit()),
		AtomVoidExpr(AtomVoidExpr.class,
				Attr.ATOMAR.bit() | Attr.IS_FINAL.bit());

		/** COMMENT */
		private Class<? extends AtomExpr<?>> cls;
		/** COMMENT */
		private int typeMap;

		/**
		 * COMMENT
		 * 
		 * @param cls COMMENT
		 * @param typeMap COMMENT
		 */
		AtomExprClass(Class<? extends AtomExpr<?>> cls, int typeMap) {
			this.cls = cls;
			this.typeMap = typeMap;
		}

		/* value methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param exprClass COMMENT
		 * 
		 * @return COMMENT
		 */
		public static AtomExprClass valueOf(Class<? extends Expression> exprClass) {
			for (AtomExprClass value : values())
				if (value.cls.equals(exprClass))
					return value;
	
			String message = "can not get expression class for class \"" + exprClass.getSimpleName() + "\"";
			Logger.getLogger(AtomExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}

		/* random getter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param returnNumber COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		public static AtomExprClass getRandom(boolean returnNumber, int depth) {
			return getTypedExprClass(0 | (returnNumber ? Attr.CAN_RETURN_NUMBER.bit() : 0), depth);
		}

		/**
		 * COMMENT
		 * 
		 * @param typeMap COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		private static AtomExprClass getTypedExprClass(int typeMap, int depth) {
			if (depth == 0)
				typeMap |= Attr.IS_FINAL.bit();

			if (typeMap == 0)
				return values()[RANDOMIZER.nextInt(values().length)];

			int typeMapCount = 0;
			for (AtomExprClass atomExprClass : values())
				if ((atomExprClass.typeMap & typeMap) == typeMap)
					++typeMapCount;

			int rand = RANDOMIZER.nextInt(typeMapCount);
			for (AtomExprClass atomExprClass : values()) {
				if ((atomExprClass.typeMap & typeMap) == typeMap) {
					if (rand == 0)
						return atomExprClass;
					else
						--rand;
				}
			}

			String message = "generated random value greater than the amount of available classes!";
			Logger.getLogger(AtomExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	};

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	@SuppressWarnings("unused")
	private static enum PrematureExprClass {
		/* premature expression classes */
		PremArrayelementExpr(PremArrayelementExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremArraylengthExpr(PremArraylengthExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremClasscastExpr(PremClasscastExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremConstructorExpr(PremConstructorExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremFieldExpr(PremFieldExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremGetfieldExpr(PremGetfieldExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremLoopStmtExpr(PremLoopStmtExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremMethodExpr(PremMethodExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit()),
		PremStmtSeqExpr(PremStmtSeqExpr.class,
				Attr.PREMATURE.bit() | Attr.CAN_RETURN_NUMBER.bit());

		/** COMMENT */
		private Class<? extends PrematureExpr> cls;
		/** COMMENT */
		private int typeMap;

		/**
		 * COMMENT
		 * 
		 * @param cls COMMENT
		 * @param typeMap COMMENT
		 */
		PrematureExprClass(Class<? extends PrematureExpr> cls, int typeMap) {
			this.cls = cls;
			this.typeMap = typeMap;
		}

		/* value methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param exprClass COMMENT
		 * 
		 * @return COMMENT
		 */
		public static PrematureExprClass valueOf(Class<? extends Expression> exprClass) {
			for (PrematureExprClass value : values())
				if (value.cls.equals(exprClass))
					return value;
	
			String message = "can not get expression class for class \"" + exprClass.getSimpleName() + "\"";
			Logger.getLogger(PrematureExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}

		/* random getter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param returnNumber COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		public static PrematureExprClass getRandom(boolean returnNumber, int depth) {
			return getTypedExprClass(0 | (returnNumber ? Attr.CAN_RETURN_NUMBER.bit() : 0), depth);
		}

		/**
		 * COMMENT
		 * 
		 * @param typeMap COMMENT
		 * @param depth COMMENT
		 * 
		 * @return COMMENT
		 */
		private static PrematureExprClass getTypedExprClass(int typeMap, int depth) {
			if (depth == 0)
				typeMap |= Attr.IS_FINAL.bit();

			if (typeMap == 0)
				return values()[RANDOMIZER.nextInt(values().length)];

			int typeMapCount = 0;
			for (PrematureExprClass premExprClass : values())
				if ((premExprClass.typeMap & typeMap) == typeMap)
					++typeMapCount;

			int rand = RANDOMIZER.nextInt(typeMapCount);
			for (PrematureExprClass premExprClass : values()) {
				if ((premExprClass.typeMap & typeMap) == typeMap) {
					if (rand == 0)
						return premExprClass;
					else
						--rand;
				}
			}

			String message = "generated random value greater than the amount of available classes!";
			Logger.getLogger(PrematureExprClass.class).fatal(message);
			throw new RandElementGeneratorException(message);
		}
	};
}
