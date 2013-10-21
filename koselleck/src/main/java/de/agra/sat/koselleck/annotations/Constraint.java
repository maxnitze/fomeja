package de.agra.sat.koselleck.annotations;

/** imports */
import static java.lang.annotation.ElementType.METHOD;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * 
 * @author Max Nitze
 */
@Target({METHOD})
@Retention(RetentionPolicy.RUNTIME)
public @interface Constraint {
	Field [] fields();
	
	public @interface Field {
		String name();
	}
}
