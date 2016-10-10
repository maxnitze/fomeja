Feature: Decompiler
	  Inside the library the decompiler is used to interpret an
	  equivalent statement sequence to a pre-parsed list of bytecode
	  expressions.

	  Scenario: Decompiling a valid list of bytecode expressions
	    Given there is a decompiler
	    And there is a list of bytecode expressions of a valid method
	    And the list of bytecode expressions is decompiled
	    Then the decompiler should yield a valid statement sequence