package de.uni_bremen.agra.fomeja.utils;

import java.io.PrintStream;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class DumpUtils {
	/**
	 * COMMENT
	 * 
	 * @param message COMMENT
	 */
	public static void dumpOut(String message) {
		dumpPrintStream(System.out, message);
	}

	/**
	 * COMMENT
	 * 
	 * @param message COMMENT
	 */
	public static void dumpErr(String message) {
		dumpPrintStream(System.err, message);
	}

	/**
	 * COMMENT
	 * 
	 * @param stream COMMENT
	 * @param message COMMENT
	 */
	public static void dumpPrintStream(PrintStream stream, String message) {
		DumpCaller dumpCaller = getDumpCaller();
		if (message != null && message.contains("\n"))
			stream.println(dumpCaller.toString() + ":\n  " + message.replaceAll("\n", "\n  "));
		else
			stream.println(dumpCaller.toString() + ": " + message);
	}

	/* private static methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private static DumpCaller getDumpCaller() {
		String clsName = null, methodName = null;
		for (StackTraceElement ste : Thread.currentThread().getStackTrace()) {
			if (!ste.getClassName().equals(Thread.class.getName())
					&& !ste.getClassName().equals(DumpUtils.class.getName())) {
				clsName = ste.getClassName();
				methodName = ste.getMethodName();
				break;
			}
		}

		return new DumpCaller(clsName != null ? clsName.replaceAll("^.*\\.(\\S+)$", "$1") : null, methodName);
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class DumpCaller {
		/** COMMENT */
		private String clsName;
		/** COMMENT */
		private String methodName;

		/**
		 * COMMENT
		 * 
		 * @param clsName COMMENT
		 * @param methodName COMMENT
		 */
		public DumpCaller(String clsName, String methodName) {
			this.clsName = clsName;
			this.methodName = methodName;
		}

		/* class methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public String toCallerString() {
			return (this.clsName != null ? this.clsName : "\"Unknown Class\"") + "#" + (this.methodName != null ? this.methodName : "\"Unknown Method\"");
		}

		/* overridden methods
		 * ----- ----- ----- ----- ----- */

		@Override
		public String toString() {
			return this.toCallerString();
		}
	}
}
