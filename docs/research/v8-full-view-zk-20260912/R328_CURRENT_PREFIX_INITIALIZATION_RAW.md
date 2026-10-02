# R328: exact selected batch prefix-initialization fragment

`AspisR328PrefixInitializationRaw.lean` compiled successfully. The source-contiguous first-vector prefix initialization from R292 batch lines 527–542 compiles unchanged inside an explicit proof harness. Only imports, namespace, function wrapper, final ok px2 and axiom print are new; all source operations/order/variables are retained with no substitutions. This fragment begins after the full batch validations; it is not a standalone Rust root and does not prove those guards, the ys branch, total inverse or full caller. Retained Aeneas library/R249/R316/R318 bindings and their explicit prior adapters are inherited.

Compile revision `e7b379f519c8ca743ad866ebdfa3e26f3fed92d4`; exit 0; wall 0:00.96; child peak RSS 2526368 KiB; swaps 0. The complete axiom report uses only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r328-current-prefix-initialization-raw/manifest.json).

First remaining proposition: Prove the fragment empty-input error and successful canonical nonempty products with capacity derived from the valid Slice bound. Then connect the actual guard and remaining source batch operations, preserving errors and Rust-library/compiler boundaries.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
