# R321: selected forward-prefix loop termination and products

`AspisV8R19/R321BatchPrefixLoopExecution.lean` compiled successfully. The actual forward prefix loop terminates and returns precisely the original prefix vector followed by each sequential encoded product. The premises explicitly specify the remaining iterator count, canonical remaining reads, encoded last prefix value, and enough vector capacity. Zero products are allowed and no nonzero premise is supplied. The model-only prefixValues list is proved to have the exact remaining length; it does not replace execution or assume a library behavior. The second source loop is definitionally equal to the first. The complete source caller and independent Rust-library/compiler correspondence are not proved.

Compile revision `51a20ccf5b15b92576bb704011286435c1644a0e`; exit 0; wall 0:01.69; child peak RSS 3716704 KiB; swaps 0. All three complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r321-current-batch-prefix-loop-execution/manifest.json).

First remaining proposition: Derive these prefix invariants and their canonical products from actual batch initialization and guard, then connect the prefix entries, total inverse and reverse-loop initialization. Preserve all-word batch errors; chain/any/default try_fold, full freeze fold/extend, callback chronology, joint privacy, shared-oracle probability accounting and soundness remain open.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
