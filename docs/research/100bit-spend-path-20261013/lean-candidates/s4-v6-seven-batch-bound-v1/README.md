# S4 V6 seven-batch bound checkpoint

This packet records a focused Lean proof chain for the isolated fixed-V6 `four_dots` candidate. The V6 term-body and enclosing-loop success are transferred to the retained emitted loop; the consumer then applies the existing seven-batch limb-bound theorem. Under the shared coordinate-bound premise, successful execution implies each returned output limb is at most seven times the per-batch cap.

The packet contains source files and exact receipts/configuration only; it does not bundle Lean objects. Direct imported object hashes and source pins are recorded in `manifest.json`. Successful checks used Lean 4.32 with capped NUC scopes (MemoryHigh 1 GiB, MemoryMax 2 GiB, swap 0). The outer seven-bound consumer is `V6OuterSevenBatchBoundV1`.

This does not establish equivalence of the fixed-V6 candidate to the frozen Rust `four_dots` implementation. In particular, the source's `core::array::from_fn` call remains an open library-correspondence boundary. No production Rust source was changed. The later P6 reviewed std-library model and its differential test are separate evidence and are not included in this checkpoint.

`evidence/attempt-v1-failed` preserves the initial missing-owner setup failure. `evidence/attempt-v3-outer` preserves the first outer-transfer attempt; the accepted corrected target and final seven-bound target have their own exact attempt evidence directories.
