# Actual tail input and loop trace

A successful actual tail body supplies its source coefficient index/read, checked slot/term offsets,16-byte slice, QM31 parser call, EbyKDot push and unwrap. The whole actual loop supplies a retained sequence of these same-state calls. For the actual0..2 range, the trace has exactly two pushes, in term order[0,1]; range exhaustion follows from source execution, not a stop premise.

The body check passed11.268s, peak process RSS2,256,879,616B. The loop/geometry check passed5.610s, peak process RSS2,263,629,824B. Zero swaps; all four public axiom reports are standard-only. One rejected small range-normalization draft is retained.

FourDotsOps remains an explicit source boundary. These facts retain the actual calls needed by concrete parser/dot arithmetic refinements; they do not assume or establish those laws, RustStd/P6 or full frozen caller/runtime soundness. No production source changed.
