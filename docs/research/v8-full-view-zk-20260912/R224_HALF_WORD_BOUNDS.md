# R224: canonical half-word bounds without a native checker

`AspisV8R19/R224HalfWordBounds.lean` compiled successfully. Symbolic low-31-bit rotation of any canonical 32-bit word w<P: exact Nat value floor(w/2)+(w mod2)*2^30, result<P, and exact unreduced identity 2*result=w+(w mod2)*P. Kernel proof uses Nat bitwise/division facts and arithmetic, no native checker or new axiom. This is a word-level predecessor, not an actual half source-method correspondence.

Compile revision `5de2ac01e31c4a42d9ae7a042e9503fbb12edec3`; exit 0; wall 1.38 s; child RSS 3,234,464 KiB; zero swaps. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. All three complete axiom reports contain only `propext` and `Quot.sound`.

The native-checker preflight (exit 0) was rejected after its axiom audit. A failed literal-rewrite draft and the wrapped-add declaration that hit Lean's internal memory cap are retained. The wrapped-add route was replaced by the simpler exact unreduced integer doubling statement; the cap was not raised and the failed unchanged target was not rerun. Details, old/new checksums, all logs, complete axiom reports and exact runner are in [the manifest](evidence/r224-half-word-bounds/manifest.json).

First remaining proposition: Extract and prove actual selected M31/CM31 half and connect the line-coordinate coefficient optimization and source array evaluation to the field algebra.

Captured gamma fold, selected vector copying, full callback chronology and end-to-end privacy/soundness remain open. Verifier source, all security parameters and 999,790 / 999,532 CU results remain preserved. No benchmark or unchanged regression suite reran.
