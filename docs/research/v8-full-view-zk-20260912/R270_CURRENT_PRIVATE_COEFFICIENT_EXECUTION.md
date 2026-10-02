# R270 selected private coefficient execution

`AspisV8R19/R270PrivateCoefficientExecution.lean` compiled successfully. On canonical encodings of every quartic triple, the actual private Coeff110 constructor returns Some of the exact five line coefficients, preserving its six Option input calls and actual norm/polar closure calls. The private four-value evaluator on these coefficients returns the exact lineFour projections for arbitrary encoded x/y/t, with no circle premise. No arbitrary-raw constructor fallback, vector traversal, batch, inverse, acceptance or whole callback theorem.

Compile revision `975d79a80fa55407cd04575bc8d3b0169d6daddc`; exit 0; wall 0:02.27; child peak RSS 3722464 KiB; swaps 0. Both complete reports use only propext, Classical.choice and Quot.sound; no sorryAx, native decision axiom or new execution premise. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r270-current-private-coefficient-execution/manifest.json).

First remaining proposition: Prove arbitrary-raw private coefficient input failures and bind the four values to actual line coordinates and source norm fibres; then actual batch/traversal and optimized-to-source acceptance.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
