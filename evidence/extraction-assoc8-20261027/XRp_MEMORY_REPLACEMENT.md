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

L094 accepts the split generic normalize/subtract/source/target equations:
exit0,1.891572244s,4765456KiB,swap0, standard axioms only. L095's further
attempt to compose whole canonical M31 subtraction in a separate module
still exhausts kernel memory: exit1,15.127367485s,7168648KiB,swap0. Its
self-axiom diagnostic is rejected. Do not retry it unchanged or raise caps.
Stop this remaining composition at the checked split equations. Addition
composition is independently checked through CM31 (L093) and QM31 (L096).
