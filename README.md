mspdetector
===========

Missing Sequence detector for C using LLV environment

Basically It detects the C expression in a code which are missing Sequence points.
Sequence ponits are important part of expression evaluation C, Sequence points removes the ambiguity in evaluation
Sequence Point :
A sequence point defines any point in a computer program's execution at which it is guaranteed that all side effects of previous evaluations will have been performed, and no side effects from subsequent evaluations have yet been performed. They are often mentioned in reference to C and C++, because the result of some expressions can depend on the order of evaluation of their subexpressions. Adding one or more sequence points is one method of ensuring a consistent result, because this restricts the possible orders of evaluation.

Hence when sequences points are missing in expression, then they become ambigous, and their result based on 
how compiler is interpreting those expressions.

Hence I wrote this tool for clang compiler which basically detect expression which are missing sequence points.
