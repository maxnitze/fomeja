package de.agra.sat.koselleck.examples.registerallocation;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Objective;

public class AssemblerCode {
	private List<Register> registers;
	
	@Constraint(fields = {})
	public boolean overlappingRegisters(Register r1, Register r2) {
		return !r1.interval.intersectsWith(r2.interval) || r1.address != r2.address || r1 == r2;
	}
	
	@Objective
	public int numberOfColors() {
		Set<Integer> addresses = new HashSet<Integer>();
		for(Register register : this.registers)
			addresses.add(register.address);
		
		return registers.size();
	}
}
