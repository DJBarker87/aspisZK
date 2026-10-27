# L091 memory failure and split replacement

L091 XRp_PowersScalarSub: exit1, wall16.046061440s, peakRSS7168652KiB,
swap0, Lean -M7000, scope6G/8G/swap0/tasks64. The source equation at line31
hit recursion depth; the subsequent composed sub theorem at line38 exhausted
kernel memory. This is rejected evidence, including its nonstandard self-axiom
diagnostic. No theorem from L091 is credited and no olean is reused.

Replacement: remove the composed sub theorem from the module, preserve it in
XRp_PowersScalarSub_FAILED.lean.txt; prove the source equation by named
bind/lift simplification instead of broad definitional comparison. Compile
only the generic normalization/subtraction stages and separate source/target
equations. Whole scalar subtraction and higher powers transport stay OPEN.
No cap is raised and the failed source is not rerun unchanged.
