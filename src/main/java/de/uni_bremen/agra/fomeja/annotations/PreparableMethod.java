package de.uni_bremen.agra.fomeja.annotations;

/* imports */
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface PreparableMethod {
	
}
