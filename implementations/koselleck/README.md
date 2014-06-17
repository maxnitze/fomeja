DIAB – Koselleck – JavaSAT
=============================

...

Supported Examples
--------------------------

### Vertex-Color

[Vertex-Color Example](../example-vertexcolor "implementation of vertex-color example")

...

### Scheduling

[Scheduling Example](../example-schedule "implementation of scheduling example")

...

Supported Bytecode-Opcodes
--------------------------

Bytecode-Opcodes are ...

- `aload_<VALUE>`

 pushes a general value <VALUE> onto the stack

- `aload <VALUE>`

 pushes a general value <VALUE> onto the stack

- `astore_<INTEGER_VALUE>`

 puts the current general value on top of the stack to the store at position <INTEGER_VALUE>

- `astore <INTEGER_VALUE>`

 puts the current general value on top of the stack to the store at position <INTEGER_VALUE>

- `bipush <BYTE_VALUE>`

 pushes a byte value <BYTE_VALUE> as an integer value onto the stack

- `checkcast`

  ...

- `dadd`

 adds the two top double values from the stack and pushes the result back

- `dcmpg`

  ...

- `dcmpl`

  ...

- `dconst_<DOUBLE_VALUE>`

 pushes a constant double value <DOUBLE_VALUE> onto the stack

- `dconst <DOUBLE_VALUE>`

 pushes a constant double value <DOUBLE_VALUE> onto the stack

- `ddiv`

 divids the two top double values from the stack and pushes the result back

- `dload_<DOUBLE_VALUE>`

 pushes a double value <DOUBLE_VALUE> onto the stack

- `dload <DOUBLE_VALUE>`

 pushes a double value <DOUBLE_VALUE> onto the stack

- `dmul`

 multiplies the two top double values from the stack and pushes the result back

- `dstore_<INTEGER_VALUE>`

 puts the current double value on top of the stack to the store at position <INTEGER_VALUE>

- `dstore <INTEGER_VALUE>`

 puts the current double value on top of the stack to the store at position <INTEGER_VALUE>

- `dsub`

 subtracts the two top double values from the stack and pushes the result back

- `dup`

  ...

- `f2d`

 converts the float value on top of the stack to a double value and pushes it back on the stack

- `fadd`

 adds the two top float values from the stack and pushes the result back

- `fcmpg`

  ...

- `fcmpl`

  ...

- `fconst_<FLOAT_VALUE>`

 pushes a constant float value <FLOAT_VALUE> onto the stack

- `fconst <FLOAT_VALUE>`

 pushes a constant float value <FLOAT_VALUE> onto the stack

- `fdiv`

 divids the two top float values from the stack and pushes the result back

- `fload_<FLOAT_VALUE>`

 pushes a float value <FLOAT_VALUE> onto the stack

- `fload <FLOAT_VALUE>`

 pushes a float value <FLOAT_VALUE> onto the stack

- `fmul`

 multiplies the two top float values from the stack and pushes the result back

- `fstore_<INTEGER_VALUE>`

 puts the current float value on top of the stack to the store at position <INTEGER_VALUE>

- `fstore <INTEGER_VALUE>`

 puts the current float value on top of the stack to the store at position <INTEGER_VALUE>

- `fsub`

 subtracts the two top float values from the stack and pushes the result back

- `getfield`

  ...

- `getstatic`

  ...

- `goto`

  ...

- `i2d`

 converts the integer value on top of the stack to a double value and pushes it back on the stack

- `i2f`

 converts the integer value on top of the stack to a float value and pushes it back on the stack

- `iadd`

 adds the two top integer values from the stack and pushes the result back

- `iconst_<INTEGER_VALUE>`

 pushes a constant integer value <INTEGER_VALUE> onto the stack

- `iconst <INTEGER_VALUE>`

 pushes a constant integer value <INTEGER_VALUE> onto the stack

- `idiv`

 divids the two top integer values from the stack and pushes the result back

- `if_acmpeq`

  ...

- `if_acmpge`

  ...

- `if_acmpgt`

  ...

- `if_acmple`

  ...

- `if_acmplt`

  ...

- `if_acmpne`

  ...

- `if_icmpeq`

  ...

- `if_icmpge`

  ...

- `if_icmpgt`

  ...

- `if_icmple`

  ...

- `if_icmplt`

  ...

- `if_icmpne`

  ...

- `ifeq`

  ...

- `ifge`

  ...

- `ifgt`

  ...

- `ifle`

  ...

- `iflt`

  ...

- `ifne`

  ...

- `iload_<INTEGER_VALUE>`

 pushes an integer value <INTEGER_VALUE> onto the stack

- `iload <INTEGER_VALUE>`

 pushes an integer value <INTEGER_VALUE> onto the stack

- `imul`

 multiplies the two top integer values from the stack and pushes the result back

- `invokespecial`

  ...

- `invokestatic`

  ...

- `invokevirtual`

  ...

- `istore_<INTEGER_VALUE>`

 puts the current integer value on top of the stack to the store at position <INTEGER_VALUE>

- `istore <INTEGER_VALUE>`

 puts the current integer value on top of the stack to the store at position <INTEGER_VALUE>

- `isub`

 subtracts the two top integer values from the stack and pushes the result back

- `ldc`

  ...

- `ldc2_w`

  ...

- `new`

  ...

- `return`

  ...

- `tableswitch`

  ...

Other Informations
------------------

- needs java 7 for javap to recognize generics in parameter types
