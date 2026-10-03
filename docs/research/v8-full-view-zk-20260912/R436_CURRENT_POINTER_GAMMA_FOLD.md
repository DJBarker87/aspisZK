# R436: stored-cell counted gamma fold

R436 composes the immutable stored-cell pointer-view model with the existing actual-field closed gamma callback and weighted-sum result. It supplies no separate load-oracle premise. This is a model composition, not a native pointer/borrow/frame/dispatch or whole Rust-fold theorem. It does not close privacy or soundness.

## Verification

Exact target: `AspisV8R19/R436PointerGammaFold.lean`. Source revision: `77857d6028d1b4016949aa14b19c17282e2cec0c`. Promoted source equals successful B, SHA256 `4aa8ca0117a4adc826ae11b5a3b4ffceace70c1cbd4f1ff84e9587598be0b5c8`.

B exited0 in1.52 seconds, GNU peak RSS3,709,252 KiB, swaps0. Terminal cgroup peak417,091,584 bytes, zero swap, no OOM/high/max events. The measures remain separate; their difference is not explained by the saved records. The complete single `#print axioms counted_pointer_gamma_fold` report lists only `propext`, `Classical.choice`, `Quot.sound`.

A exited1 in1.51 seconds, GNU peak RSS3,695,852 KiB, swaps0: a redundant `rfl` after the preceding rewrite reported “No goals to be solved”. Its standard-only axiom report does not make that run successful. B removes that extra tactic without changing the theorem, premises or proof route. Both exact sources, logs, commands, metrics and statuses are retained. Successful checks were not rerun unchanged.

The jobs used pinned Lean4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, cached workspace, `lake env lean -j1 -M4500`, MemoryHigh5 GiB, MemoryMax7 GiB, MemorySwapMax0, TasksMax128. Source equality, complete axiom output, six copy receipts and effective resource limits passed independent custody and lead audits.

## Precise theorem boundary

Premises are a modeled allocation present in the heap, a range bounded by its stored cell length, and equality of that range's cell view to an encoded list of exact QM31 values. The initial accumulator, power and gamma are encoded exact values. R432 derives every in-bounds pointer load from stored cells and makes the arbitrary unsupported-read fallback unreachable. R184 supplies the closed callback fold result and weighted-sum identity. The result is exactly the encoded initial accumulator plus initial power times the gamma-weighted sum.

The encoded cell-view premise is explicit; it is not silently inferred from the source Wire. The heap remains immutable by the pointer model, and the callback is the closedGamma representation. Actual source allocation/value images, captured mutable-reference restoration, storage frame, native callback dispatch, ABI and pointer semantics remain obligations. The proof invokes the counted pointer-view theorem, not the default Rust iterator implementation. Existing weighted-sum and field proofs are reused without replay.

## First remaining proposition

Connect the actual source constructor/fold and callback to these representations, preserving pointer validity, metadata/casts/distance, unchecked successor bounds, borrow restoration, frame and complete check/drop/unwind/error behavior. R437 exposes pointer-wrapper source layout before any ABI or cast equivalence is claimed. Vec::extend and whole callback/oracle chronology remain open.

Universal joint C1/H1/G compatibility, the entire published-view simulator and shared-oracle losses, coherent pre-beta original quotient extraction and optimized-to-source acceptance remain unproved. Genuine 999,790 / 999,532 CU and all security parameters are preserved. No benchmark, unchanged regression, deployment, merge, transaction or wallet operation occurred.
