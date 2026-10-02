# R340: both original output setup fragments

`AspisR340BatchOutputRaw.lean` compiled successfully. The original clone method/instance and both source-contiguous output allocation, reverse-range, reverse-loop and index-zero-store fragments compile unchanged. Source helper names remain bound to the previously verified selected reverse loops and pinned Aeneas library definitions; no operation is substituted. This raw result does not prove source output lengths/bounds, whole-batch guards or success, or independent Rust-standard-library/compiler correspondence.

Compile revision `40a051e060c400dc65d9ada197bdff94d26d8d5b`; exit 0; wall 0:01.06; child peak RSS 2531348 KiB; swaps 0. The two exact clone definitions have no axioms; both output wrappers use only propext, Classical.choice and Quot.sound. No sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r340-current-batch-output-raw/manifest.json).

First remaining proposition: Prove original from_elem/reverse-range/index-zero setup establishes both reverse-loop caller invariants and its exact output Result; then bind source prefixes/shared inverse and actual traversal guards.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
