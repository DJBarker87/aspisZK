# R324: selected forward-prefix complete Result correspondence

`AspisV8R19/R324BatchPrefixComplete.lean` compiled successfully. Both actual forward-prefix loops equal a finite Result recurrence over the exact remaining count. The correspondence retains every unwrap, multiplication and push failure or divergence at its original stopping point. It assumes only the remaining-count relation and exact raw source reads, without canonicality, capacity, nonzero or success premises. The recurrence uses retained executable helpers rather than new execution assumptions. Independent Rust-library/compiler correspondence and the complete batch caller remain open.

Compile revision `469bdd2cdd73f88385114074e27e1f9e566c3022`; exit 0; wall 0:01.61; child peak RSS 3716960 KiB; swaps 0. All 2 complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r324-current-batch-prefix-complete/manifest.json).

First remaining proposition: Discharge the purely indexing/count premises for every raw iterator/vector state, then derive batch guard, initialization and inverse/reverse connections from actual source.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
