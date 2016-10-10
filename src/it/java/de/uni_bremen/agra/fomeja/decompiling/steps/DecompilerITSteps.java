package de.uni_bremen.agra.fomeja.decompiling.steps;

import cucumber.api.PendingException;
import cucumber.api.java.en.Then;
import cucumber.api.java.en.When;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class DecompilerITSteps {
    @When("^there is a decompiler$")
    public void there_is_a_decompiler() throws Throwable {
        throw new PendingException("not yet implemented");
    }
 
    @When("^there is a list of bytecode expressions of a valid method$")
    public void there_is_valid_bytecode_list() throws Throwable {
        throw new PendingException("not yet implemented");
    }
    
    @When("^there is a list of bytecode expressions of a invalid method$")
    public void there_is_invalid_bytecode_list() throws Throwable {
        throw new PendingException("not yet implemented");
    }
    
    @When("^the list of bytecode expressions is decompiled$")
    public void the_bytecode_list_is_decompiled() throws Throwable {
        throw new PendingException("not yet implemented");
    }
 
    @Then("^the decompiler should yield a valid statement sequence$")
    public void the_result_should_be(int arg1) throws Throwable {
        throw new PendingException("not yet implemented");
    }
}
