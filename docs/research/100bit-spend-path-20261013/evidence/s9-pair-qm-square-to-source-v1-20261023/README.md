# Pair caller QM square to extracted source cut

This focused proof maps the frozen Pair caller’s `QM31.square` full `Result` at one operand to the extracted attempt-19 square source cut. It composes the existing Pair-caller-to-P6 operation bridge with the helper-to-source square bridge and explicit carrier round trips. The theorem requires canonicality for the same P6-mapped operand.

This is an operation-level source-cut correspondence for the caller’s square call. It does not establish the full caller/body or loop refinement, nor a deployed-binary refinement.

The central Lean run exited 0 in 16.410 seconds, with 3,255,189,504 bytes peak aggregate RSS and zero swaps. The exported theorem reports `[propext, Classical.choice, Quot.sound]`. Exact source/object hashes, controller, command, profile, preflight, closure, and process metrics are retained under `proof/`. Compiled objects are not included.
