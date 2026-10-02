# R305 raw reverse-loop staging

This scratch adapter contains the exact generated declaration blocks for R292 `batch_loop2.body`, `batch_loop2`, `batch_loop3.body`, and `batch_loop3`. The deterministic builder checks the saved Funs input SHA before extracting the blocks. No bodies were rewritten; four `#print axioms` commands were appended.

The adapter imports `Aeneas.Std` and `AspisR249R110Raw` and is **not compiled**. The binding audit records that R292's and R249's `B` aliases both reduce to `Std.U32`, and their `B.mul` signatures match after unfolding. Their implementations differ at the shift-count literal (`31#i32` in R292, `31#u32` in R249); the staged blocks call the imported R249 definition. This is a mechanical signature/body comparison, not a semantic-equivalence result.

Every standard-library iterator, dictionary, vector/slice operation, scalar operation, and loop used by the staged bodies is treated as a pinned Aeneas library dependency. Executable Aeneas definitions such as `Rev.next` and `Range.next_back` are not thereby proved to correspond to Rust. The staging does not close the actual batch traversal and establishes no reverse-loop invariant or source refinement.

Inputs and their hashes, extracted declaration spans, and block hashes are listed in `staging-audit.json` and `binding-audit.json`. `build_raw.py` is the deterministic extraction builder. This task did not run Lean.
