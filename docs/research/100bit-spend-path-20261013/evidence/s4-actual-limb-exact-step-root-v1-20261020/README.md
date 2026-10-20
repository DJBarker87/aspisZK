# Exact emitted limb accumulator update

A successful actual inner-limb body advances its cursor by one, preserves the end bound, adds exactly the actual coefficient×scalar to the visited accumulator cell, and leaves every other cell unchanged. The proof reuses the existing actual widened multiply/add/update facts and checked array semantics. It replaces no source code and assumes no output equation.

Focused V2: exit0, 3.554 seconds, process RSS2,255,208,448 bytes, zero swaps; standard axioms only. Exact launch revision, source/object/import pins and command are retained. The required canonical input and current-cell range bounds remain explicit and are supplied by the existing term-body proof. The full eight-limb loop lift and per-term equation are next. No production source/artifact/CU changed.
