# R243 point-derived line arithmetic and retained norms

`AspisV8R19/R243LineNormBridge.lean` compiled successfully. The composed raw multiply/double/subtract fragment returns encoded 2*x^2-1. Composing this with the actual retained LineCoeff constructor/evaluator gives the exact ordered R218 four-value algebra. Under the explicit base-field circle premise x^2+y^2=1, the four outputs are precisely the quartic norms of the four ordered affine sign fibres. No nondegeneracy condition is needed. This is a manually composed arithmetic fragment with selected generated leaves; it does not establish whole source point-loop traversal, shared vector provenance, private R110 execution or optimized acceptance.

Compile revision `f9087a48505a8fb6a3af8c27f3f9ee8f925ed79f`; exit 0; wall 0:01.79; child peak RSS 3718732 KiB; swaps 0. All four complete axiom reports use only propext, Classical.choice and Quot.sound; no source execution premise, sorryAx or native decision axiom. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r243-retained-line-norm-bridge/manifest.json).

First remaining proposition: Prove actual selected point and vector traversal supplies these shared coordinates, and bind the private R110 fast path and inverse batch to the same denominators.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
