# R341: exact nonzero criterion for both prefix products

`AspisV8R19/R341PrefixNonzero.lean` compiled successfully. For every field-valued source-index function and prefix index, its sequential sourcePrefixValue is nonzero exactly when every element through that index is nonzero. For two positive source lengths, the shared total product is nonzero exactly when every element in both input index ranges is nonzero. The symbolic recurrence and field no-zero-divisor law prove the criterion without concrete reduction. These are algebraic statements only; no actual iterator guard success or caller execution is assumed proved.

Compile revision `37d5dd7ecb2c6f7b98822147522b043884ef77d9`; exit 0; wall 0:01.57; child peak RSS 3710056 KiB; swaps 0. All three complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r341-current-prefix-nonzero/manifest.json).

First remaining proposition: Bind the actual source zero-detection traversal to the two universal input nonzero conditions; then apply this criterion to the actual shared inverse result, retaining every guard/error/stop. Complete output setup, actual callback and privacy/soundness obligations.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
