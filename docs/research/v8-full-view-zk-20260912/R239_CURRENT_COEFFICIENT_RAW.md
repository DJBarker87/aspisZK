# R239 selected coefficient leaves

`AspisR239CoeffExecutionRaw.lean` compiled successfully. Seven selected generated leaf definitions and two ground shift-count equalities compile. R231 extraction is retained; R232 empty translation is rejected; R237 changes only declaration-order metadata and was independently audited; R238 produces the selected bodies. R239 retains those bodies with two explicit signed-to-unsigned shift-count API adaptations (1 and 30). Recursively bound R156/R221 project declarations match, with the already recorded M31.mul count-31 API adaptation. Compilation of definitions alone does not prove execution correspondence.

Compile revision `f3ffde1f52bab63d1d561515f06978c2bb097291`; exit 0; wall 0:01.10; child peak RSS 2538892 KiB; swaps 0. All complete axiom reports contain only propext, Classical.choice and Quot.sound (subsets allowed). No sorryAx, native decision axiom or execution assumption is admitted. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r239-current-coefficient-raw/manifest.json).

First remaining proposition: Prove canonical half/scalar multiplication execution and the coefficient constructors/evaluations, then the actual selected inverse including its private R110 fast path and retained fallback.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
