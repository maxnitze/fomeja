Fomeja -- Formal Methods within Java
====================================

[![Build Status](https://travis-ci.org/razr69/fomeja.svg?branch=master)](https://travis-ci.org/razr69/fomeja)
[![Coverity Scan Build Status](https://scan.coverity.com/projects/8470/badge.svg)](https://scan.coverity.com/projects/fomeja)
[![Maven Central](https://img.shields.io/maven-central/v/de.uni_bremen.agra.fomeja/fomeja.svg)](http://mvnrepository.com/artifact/de.uni_bremen.agra.fomeja/fomeja)

With formal methods complex problems can be solved exactly, but today most
tools are not easy to use and claim a deep understanding of the problem and
the underlying algorithms.

With this tool we try to introduce a method to use formal methods without
leaving the familiar environment of a common programming language, in this case
Java.

...

Installation and Running
------------------------

To run this framework we need some object files from the `Z3` installation,
namely `libz3.so` and `libz3java.so`.


If you have `Z3` installed, we just need the path to your `bin` directory
within the installation.

Otherwise just clone the `Z3` repository on github
(https://github.com/Z3Prover/z3) and build it as described in the README.

When running a program using this framework we need to add the directory
containing the two `.so` files to the `LD_LIBRARY_PATH` environment variable.
For example:
```bash
LD_LIBRARY_PATH=/opt/z3/bin java -jar ...
```

Other Informations
------------------

- To recognize generics from the bytecode (important for all kinds of
collections), this tool needs Java 7 as a runtime environment (especially the
javap binary from that package).
