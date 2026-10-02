# R279 selected private scalar negation and inverse

`AspisV8R19/R279PrivateScalarInverse.lean` compiled successfully. On canonical encoded M31 inputs, the actual private negation returns the exact field negative. The actual private inverse returns the exact inverse for nonzero inputs, while zero retains the selected source assertion failure. Nonzero is explicit and has not been inferred from an unproved batch guard. No batch/traversal or whole callback correspondence.

Compile revision `e8601f2d13149484f3a6a0304cd48892821363c4`; exit 0; wall 0:01.45; child peak RSS 3705148 KiB; swaps 0. All three complete reports use only propext, Classical.choice and Quot.sound; no sorryAx, native decision axiom or new execution premise. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r279-current-private-scalar-inverse/manifest.json).

First remaining proposition: Bind actual point traversal, original denominator vectors, zero guards, prefix/reverse batch loops and shared inversion to the selected-source result; then full callback chronology, universal joint privacy and soundness.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
