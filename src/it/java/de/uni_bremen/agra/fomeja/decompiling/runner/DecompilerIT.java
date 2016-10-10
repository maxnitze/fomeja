package de.uni_bremen.agra.fomeja.decompiling.runner;

import org.junit.runner.RunWith;

import cucumber.api.CucumberOptions;
import cucumber.api.junit.Cucumber;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
@RunWith(Cucumber.class)
@CucumberOptions(
		plugin = { "pretty", "html:target/cucumber" },
		glue = { "de.uni_bremen.agra.fomeja.decompiling.steps" },
		features = "src/it/resources/cucumber/decompiler.feature")
public class DecompilerIT {

}
