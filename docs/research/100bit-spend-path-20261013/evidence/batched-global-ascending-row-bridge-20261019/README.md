# Global raw bounds supply an ascending actual row fold

The range traversal constructs distinct ascending row visits for indices 0 through n-1. The explicit index identity, row-count bound and canonical operands turn one global phase-wide raw-cell bound into the precise per-visit admissibility conditions. The published distinct-row transport then constructs a SafeRows execution of the actual generated pushes.

This still requires correspondence of the source caller's concrete index/value projections, initialization and phase-wide invariant, and checked counter increment. It does not claim the Rust caller as a whole has been extracted or proved.

The two focused Lean 4.32 checks exited 0 in 8.69 and 3.60 seconds, peak RSS at most 2,242,527,232 bytes, zero process swaps and standard printed axioms only. Exact target/source/object/import pins, commands and logs are retained. This is focused working evidence, not a unified release replay.
