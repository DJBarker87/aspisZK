# R236: unsigned wrapping half-word operations

`AspisV8R19/R236HalfWordOps.lean` compiled successfully. For every raw U32 word, the explicit unsigned wrapping right shift by one, mask by one, wrapping left shift by thirty and bitwise-or exactly equal the R228 halfScalar operation. No canonical-input premise is needed for this operation identity. This is a primitive operation predecessor; no actual selected Rust half declaration or signed-shift extraction correspondence is asserted.

Compile revision `e6745cf159bce98fa21a03d369548788d8546c77`; exit 0; wall 0:01.45; child peak RSS 3699384 KiB; swaps 0. The complete axiom report contains only propext, Classical.choice and Quot.sound. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r236-half-word-ops/manifest.json).

First remaining proposition: Bind the selected half declaration with its actual generated operand types, then compile actual Coeff/LineCoeff construction and four-array execution after the declaration-order metadata audit.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
