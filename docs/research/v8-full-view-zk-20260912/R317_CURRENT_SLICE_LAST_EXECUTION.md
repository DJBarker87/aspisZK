# R317: complete generic source Slice.last execution

`AspisV8R19/R317SliceLastExecution.lean` compiled successfully. For every valid Slice T, the emitted actual Slice.last body returns exactly ok xs.val.getLast?. Empty slices return none; all nonempty valid slices return the last element. The original length guard suffices to prove checked subtraction and indexing succeed. No nonempty, canonical-field, success, or additional execution premise is supplied. The result is under the retained Aeneas primitive/library extraction model, not a verified Rust compiler theorem or complete batch/freeze correspondence.

Compile revision `b268da1cb6878d9b1ab6c2cab79b0592d04dd0ca`; exit 0; wall 0:01.15; child peak RSS 2533560 KiB; swaps 0. All complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or additional execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r317-current-slice-last-execution/manifest.json).

First remaining proposition: Bind and prove both actual forward prefix loops using this sourceful Slice.last result, then connect their prefix entries and initialization to the already-proved reverse loops. Chain/any traversal, full batch guard/total inverse, unresolved fold/extend and callback chronology remain open.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
