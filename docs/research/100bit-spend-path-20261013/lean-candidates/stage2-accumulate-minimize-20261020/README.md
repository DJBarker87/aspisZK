# Accumulator extraction minimization

Candidate-only diagnostics built from the exact frozen accumulator source-cut input and pinned field types. Variants progressively remove basis construction, the `Option<&mut BatchedWeights>` loop branch, and trace calls from the actual outer accumulator update. The initial variant has the basis-construction loop removed yet still reproduces Aeneas's `InterpBorrows.ml:2731` assertion on the outer loop. No production edits or semantic theorem are claimed.
