DIAB – Koselleck – JavaSAT
=============================

...

Supported Examples
--------------------------

### Vertex-Color

The Vertex-Color problem describes the question how many colors do I need to
color the vertices of a given graph regarding that two vertices, that have a
edge connecting them, are not allowed to have the same color.

For example having a class for the vertices with a attribute color marked as variable:

~~~java
public class Vertex {
	@Variable
	private int color;
}
~~~

And a class `Edge` containing the two vertices it connects:

~~~java
public class Edge {
	private Vertex vertex1;
	private Vertex vertex2;
}
~~~

With a class that contains all vertices and edges of a graph:

~~~java
public class Graph {
	private List<Vertex> vertices;
	private List<Edge> edges;
	
	...
}
~~~

One can define the constraints for the given problem:

~~~java
public class Graph {
	private List<Vertex> vertices;
	private List<Edge> edges;
	
	@Constraint
	public boolean adjacentHaveDifferentColors(CGEdge edge) {
		return edge.getVertex1().getColor() != edge.getVertex2().getColor();
	}
}
~~~

For a complete example look for
[Vertex-Color Example](/maxnitze/diab/tree/master/implementations/examples/example-vertexcolor "implementation of vertex-color example")
in this Project

### Scheduling

Scheduling is ...

~~~java
public class Task {

}
~~~

For a complete example look for
[Scheduling Example](/maxnitze/diab/tree/master/implementations/examples/example-schedule "implementation of scheduling example") as an example in this Project
in this Project

Supported Bytecode-Opcodes
--------------------------

Bytecode-Opcodes are ...

- `aload_<VALUE>`

 pushes a general value `<VALUE>` onto the stack

- `aload <VALUE>`

 pushes a general value `<VALUE>` onto the stack

- `areturn`

 returns the top general value from the stack

- `astore_<INTEGER_VALUE>`

 puts the current general value on top of the stack to the store at position `<INTEGER_VALUE>`

- `astore <INTEGER_VALUE>`

 puts the current general value on top of the stack to the store at position `<INTEGER_VALUE>`

- `bipush <BYTE_VALUE>`

 pushes a byte value `<BYTE_VALUE>` as an integer value onto the stack

- `checkcast <CONSTANT_TABLE_INDEX>`

 checks whether the value on top of the stack is assignable from the class value stored at the index `<CONSTANT_TABLE_INDEX>` in the constant table

- `dadd`

 adds the two top double values from the stack and pushes the result back

- `dcmpg`

 compares the two top values of the stack (treated as double values)

- `dcmpl`

 compares the two top values of the stack (treated as double values)

- `dconst_<DOUBLE_VALUE>`

 pushes a constant double value `<DOUBLE_VALUE>` onto the stack

- `dconst <DOUBLE_VALUE>`

 pushes a constant double value `<DOUBLE_VALUE>` onto the stack

- `ddiv`

 divids the two top double values from the stack and pushes the result back

- `dload_<DOUBLE_VALUE>`

 pushes a double value `<DOUBLE_VALUE>` onto the stack

- `dload <DOUBLE_VALUE>`

 pushes a double value `<DOUBLE_VALUE>` onto the stack

- `dmul`

 multiplies the two top double values from the stack and pushes the result back

- `dreturn`

 returns the top double value from the stack

- `dstore_<INTEGER_VALUE>`

 puts the current double value on top of the stack to the store at position `<INTEGER_VALUE>`

- `dstore <INTEGER_VALUE>`

 puts the current double value on top of the stack to the store at position `<INTEGER_VALUE>`

- `dsub`

 subtracts the two top double values from the stack and pushes the result back

- `dup`

  duplicates the top value of the stack and pushes the duplicate back on

- `f2d`

 converts the float value on top of the stack to a double value and pushes it back on the stack

- `fadd`

 adds the two top float values from the stack and pushes the result back

- `fcmpg`

 compares the two top values of the stack (treated as float values)

- `fcmpl`

 compares the two top values of the stack (treated as float values)

- `fconst_<FLOAT_VALUE>`

 pushes a constant float value `<FLOAT_VALUE>` onto the stack

- `fconst <FLOAT_VALUE>`

 pushes a constant float value `<FLOAT_VALUE>` onto the stack

- `fdiv`

 divids the two top float values from the stack and pushes the result back

- `fload_<FLOAT_VALUE>`

 pushes a float value `<FLOAT_VALUE>` onto the stack

- `fload <FLOAT_VALUE>`

 pushes a float value `<FLOAT_VALUE>` onto the stack

- `fmul`

 multiplies the two top float values from the stack and pushes the result back

- `freturn`

 returns the top float value from the stack

- `fstore_<INTEGER_VALUE>`

 puts the current float value on top of the stack to the store at position `<INTEGER_VALUE>`

- `fstore <INTEGER_VALUE>`

 puts the current float value on top of the stack to the store at position `<INTEGER_VALUE>`

- `fsub`

 subtracts the two top float values from the stack and pushes the result back

- `getfield <CONSTANT_TABLE_INDEX>`

 gets the value of the field at the index `<CONSTANT_TABLE_INDEX>` in the constant table starting at the top object on the stack

- `getstatic <CONSTANT_TABLE_INDEX>`

 gets the value of the field at the index `<CONSTANT_TABLE_INDEX>` in the constant table starting at the top class on the stack

- `goto <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines

- `i2d`

 converts the integer value on top of the stack to a double value and pushes it back on the stack

- `i2f`

 converts the integer value on top of the stack to a float value and pushes it back on the stack

- `iadd`

 adds the two top integer values from the stack and pushes the result back

- `iconst_<INTEGER_VALUE>`

 pushes a constant integer value `<INTEGER_VALUE>` onto the stack

- `iconst <INTEGER_VALUE>`

 pushes a constant integer value `<INTEGER_VALUE>` onto the stack

- `idiv`

 divids the two top integer values from the stack and pushes the result back

- `if_acmpeq <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the two top general values of the stack are equal

- `if_acmpge <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second general values of the stack is greater equal to the first

- `if_acmpgt <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second general values of the stack is greater than the first

- `if_acmple <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second general values of the stack is lower equal to the first

- `if_acmplt <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second general values of the stack is lower than the first

- `if_acmpne <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the two top general values of the stack are not equal

- `if_icmpeq <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the two top integer values of the stack are equal

- `if_icmpge <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second integer values of the stack is greater equal to the first

- `if_icmpgt <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second integer values of the stack is greater than the first

- `if_icmple <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second integer values of the stack is lower equal to the first

- `if_icmplt <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the second integer values of the stack is lower than the first

- `if_icmpne <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the two top integer values of the stack are not equal

- `ifeq <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the top value of the stack is equal to 0

- `ifge <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the top value of the stack is greater or equal to 0

- `ifgt <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the top value of the stack is greater 0

- `ifle <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the top value of the stack is lower or equal to 0

- `iflt <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the top value of the stack is lower 0

- `ifne <OFFSET>`

 jumps to the position `<OFFSET>` of the bytecode lines if the top value of the stack is not equal to 0

- `iload_<INTEGER_VALUE>`

 pushes an integer value `<INTEGER_VALUE>` onto the stack

- `iload <INTEGER_VALUE>`

 pushes an integer value `<INTEGER_VALUE>` onto the stack

- `imul`

 multiplies the two top integer values from the stack and pushes the result back

- `invokespecial <CONSTANT_TABLE_INDEX>`

 invoke the class-method given by the constant table at index `<CONSTANT_TABLE_INDEX>` on the object value on top of the stack

- `invokestatic <CONSTANT_TABLE_INDEX>`

 invoke the static method given by the constant table at index `<CONSTANT_TABLE_INDEX>` on the class value on top of the stack

- `invokevirtual <CONSTANT_TABLE_INDEX>`

 invoke the class-method given by the constant table at index `<CONSTANT_TABLE_INDEX>` on the object value on top of the stack

- `ireturn`

 returns the top integer value from the stack

- `istore_<INTEGER_VALUE>`

 puts the current integer value on top of the stack to the store at position `<INTEGER_VALUE>`

- `istore <INTEGER_VALUE>`

 puts the current integer value on top of the stack to the store at position `<INTEGER_VALUE>`

- `isub`

 subtracts the two top integer values from the stack and pushes the result back

- `ldc <CONSTANT_TABLE_INDEX>`

 pushes the constant from the constant table at index `<CONSTANT_TABLE_INDEX>` on top of the stack

- `ldc2_w <CONSTANT_TABLE_INDEX>`

 pushes the constant from the constant table at index `<CONSTANT_TABLE_INDEX>` on top of the stack

- `new <CONSTANT_TABLE_INDEX>`

 pushes a new instance of the class from the constant table at index `<CONSTANT_TABLE_INDEX>` onto the stack

- `tableswitch`

 starts a switch-case statement based on the top value of the stack; the next lines indicate where to jump to if the value of the respective line matches the top stack-value

Other Informations
------------------

- needs java 7 for javap to recognize generics in parameter types
