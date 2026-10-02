# R249 selected private R110 arithmetic definitions

`AspisR249R110Raw.lean` compiled successfully. Sixteen selected private B/C leaf definitions, both globals, two representation aliases and three ground shift-count equalities compile. The source extraction uses exact frozen hashes/flags. Independently audited R246 changes only ordering metadata for a stated primitive subset; C::input remains in the row table and is explicitly excluded/unproved. R247 emits nonempty generated bodies. R249 binds identical field helpers to pinned R156 and records six wrapping-operation qualification bindings plus three signed-to-unsigned count adaptations (1,30,31). Compilation of definitions alone is not an execution theorem or optimized acceptance proof.

Compile revision `26d6d454d6e0897fdf5d0fea9d5c119117602e05`; exit 0; wall 0:01.27; child peak RSS 2544008 KiB; swaps 0. Complete reports cover all 23 requests: three have no axioms; the other twenty use only propext, Classical.choice and Quot.sound. No new opaque operation, execution assumption, sorryAx or native decision axiom. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r249-current-private-arithmetic-raw/manifest.json).

First remaining proposition: Prove the private canonical arithmetic and Option input machinery, then Coeff110, actual batch/vector traversal and the complete selected inverse/acceptance route.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
