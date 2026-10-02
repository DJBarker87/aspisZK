# R316: emitted actual generic Slice.last body

`AspisR316SliceLastRaw.lean` compiled successfully. The retained generic Slice.last source row emits and compiles after the explicit one-identifier generated Usize.sub to existing UScalar.sub API adapter. Its signature, length guard, two length reads, subtraction, indexed read and Option result are retained. R312 lowers only the exact safe shared-slice Len shape through the existing unique slice_len_fn dependency; the original projected source rows remain unchanged. No external execution axiom, fresh type or invented Slice.last semantics is used. This is an extraction/elaboration leaf, not a verified compiler or whole batch result.

Compile revision `b268da1cb6878d9b1ab6c2cab79b0592d04dd0ca`; exit 0; wall 0:01.00; child peak RSS 2526400 KiB; swaps 0. All complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or additional execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r316-current-slice-last-raw/manifest.json).

First remaining proposition: Prove the emitted result for every valid slice, discharging subtraction and index safety from the original guard, then use it in the actual forward prefix loops.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.

Subsequent result: [R317](R317_CURRENT_SLICE_LAST_EXECUTION.md) proves the universal valid-slice result, including all guard/subtraction/index safety. The raw staging audit describes its pre-compilation boundary; the promoted manifest and logs record the successful root compilation.
