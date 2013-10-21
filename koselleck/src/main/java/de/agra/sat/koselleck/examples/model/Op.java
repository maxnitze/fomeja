package de.agra.sat.koselleck.examples.model;

public abstract class Op {
	public static boolean xor(boolean... booleans) {
		if(booleans.length <= 0)
			return true;
		
		boolean ret = booleans[0];
		for(int i=1; i<booleans.length; i++) {
			if(ret == booleans[i])
				ret = false;
			else
				ret = true;
		}
		
		return ret;
	}
	
	public static boolean xxor(boolean... booleans) {
		boolean ret = false;
		
		for(boolean bool : booleans) {
			if(bool == true) {
				if(ret == true)
					return false;
				else
					ret = true;
			}
		}
		
		return ret;
	}
}
