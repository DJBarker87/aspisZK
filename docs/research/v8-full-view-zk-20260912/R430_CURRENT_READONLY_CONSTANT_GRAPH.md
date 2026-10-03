# R430: readonly constants for the actual freeze fold

R430 proves evaluation of the finite readonly constant graph captured in R429, within an explicit Lean constant-fragment model. The model returns SIZE=16 and IS_ZST=false for the selected x86_64 QM31 type. It also proves replacement of each modeled scalar read in an arbitrary caller continuation. It does not prove Rust compiler correctness, source pointer execution, the entire fold, privacy, or soundness.

## Compilation and source identity

Target: `AspisV8R19/R430ReadonlyConstantGraph.lean`. Source revision at compilation: `367345a0407f8869375dcd2f30fda36ca6c4dfcb`. Exact Lean source SHA256: `9bb531624461a6ba3d6605a870f779d5cc603ab670551dd44c3755c718dc7335`.

The one focused compilation exited 0 in 1.90 seconds. GNU time records maximum RSS 2,541,012 KiB and zero swaps. The separately saved cgroup peak is 370,274,304 bytes; these distinct measurements are retained as reported. The saved records do not explain their difference, and no explanation is asserted. Effective MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128, with no OOM events. Lean is 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, using the pinned cached workspace and `lake env lean -j1 -M4500`. All six evidence-copy receipts exited 0. No unchanged successful Lean target, regression or CU benchmark was rerun.

All 12 complete `#print axioms` reports are saved in `constant-proof/attempt-a/lean.log` and the receipt. Their only dependencies are standard `propext`, `Classical.choice`, and `Quot.sound`; some definitions require fewer or none. No sorry or additional axiom is introduced. Seven theorems prove the size intrinsic model, both initializer/global results, and the two arbitrary-continuation equalities.

## Actual-source binding and primitive boundary

The 27-check source-fragment audit binds the exact successfully compiled Lean bytes and finite model tables to R429 C's native graph, SHA256 `c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465`. It verifies the x86_64 little-endian target, QM31 type 2/layout size 16/alignment 4, functions 142/145/153, globals 31/32, all five monomorphic QM31 instantiations, scalar result types, initializer statement order, preserved SIZE unwind edge and four scalar Copy reads in actual fold function 70. This is a structural source-to-model audit, not a kernel proof of an LLBC interpreter or Rustc.

The explicit `sizeOf` model rule uses the captured target layout. Saved pinned compiler source supports that rule: the CTFE intrinsic handler takes instantiated type argument 0, queries `layout_of`, reads `layout.size.bytes()`, and writes `Scalar::from_target_usize`. The scalar constructor uses the target pointer width. Integer Eq compares converted scalar values. Saved Charon source separately queries Rustc layout for the instantiated, normalized type and attaches size/alignment to its target record. This source inspection is not a formal proof of those compiler paths or their equivalence to Lean.

The model deliberately contains only scalar constants, calls, global initializer references and equality. `None` is an incomplete/unsupported-fragment diagnostic, not an invented Rust runtime error. Continuation equality is within this model; it does not establish general source lowering correctness. No translator change or constant lowering was applied.

The compiler inventory initially contained a one-character checksum typo in its JSON index. The saved source and SHA256SUMS agreed; the typo was corrected, both indexes were checked, and the failed validation is retained. The initial evidence-audit parser also produced two false negatives; its output is retained and the corrected audit matches the raw records. All evidence and API inventories remain explicit about unsupported source operations.

## First remaining proposition

Establish source execution of the captured actual specialized fold, first binding valid slice/iterator construction to its pointer/end representation and proving its source element loads, empty/length tests and unchecked arithmetic. Preserve checks, errors, unwind/drop paths, and the mutable closure's power restoration. R430 supplies only the verified constant-model fragment; it does not discharge this proposition. Reuse existing R174/R184/R191 arithmetic/closure, R193 control and R195 index results without replaying unchanged checks. The separate Vec::extend operation remains unresolved.

The pinned Aeneas library's raw-pointer wrapper is not an implemented pointer arithmetic semantics. Unsupported operations returning undef and a slice unchecked helper containing sorry cannot justify the actual fold. The saved pointer/global API inventories document those boundaries; no assumption replacing a complete library contract is accepted here.

Whole freeze chronology and inverse Domain behavior, callback/oracle chronology through rho, universal joint C1/H1/G compatibility including p0/p2 and adaptive/degenerate prefixes, a faithful whole published-view simulator with shared-oracle probability losses, coherent pre-beta quotient extraction and optimized-to-source acceptance remain open. The genuine 999,790 / 999,532 CU results and every security parameter are preserved. No deployment, merge, transaction or wallet operation occurred.
