package de.agra.sat.koselleck.annotations;

/** imports */
import static java.lang.annotation.ElementType.FIELD;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * 
 * @author Max Nitze
 */
@Target({FIELD})
@Retention(RetentionPolicy.RUNTIME)
public @interface Variable {
	
}
