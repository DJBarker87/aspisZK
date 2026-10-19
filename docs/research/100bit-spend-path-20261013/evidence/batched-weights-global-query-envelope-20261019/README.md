# Global accumulator envelope across ascending rows and repeated queries

The selected-row phase bounds, flush-lane bounds and nonselected-row frame proofs now compose across every row of an ascending range. A repeated-query induction preserves the global raw-limb envelope, array length and exact terms counter. Each checked counter increment is derived from the initial counter-room bound rather than independently assumed at every step.

These theorems operate on a query model assembled from actual extracted push operations. They do not yet establish identity with the whole Rust push_query or current caller execution. Canonical power/basis inputs, row-count alignment, initial global bounds and counter room remain premises; the indexed loop/source correspondence and initial constructor proof remain open. In particular, comments describing actual operations must not be interpreted as an accepted whole-caller extraction theorem.

Eight focused Lean 4.32 checks exited zero, with nine printed theorem axiom reports using only standard axioms. Source/object/import pins, revisions, commands, wall times, peak RSS and zero process swaps are recorded. No full frozen-manifest replay or source/runtime release claim is made.
