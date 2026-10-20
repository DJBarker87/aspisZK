# Original emitted polynomial through the concrete finish consumer

This is a source-only Lean evidence packet for `AeneasOriginalPolynomialFinishBridgeV1`. It imports the frozen original polynomial's operational adapter and the already checked `CurrentFinishCandidateUnrolledPolynomialV4` consumer. The body adapter is documented and source-checked in the adjacent `original-polynomial-fold-adapter-v2-evidence` packet (manifest `e22519a7…`); that packet pins frozen verifier.rs span `[12595,12695)`, generated full function/callback, and the remaining Rust std `Rev.fold` correspondence.

This bridge maps the operational body result through `toFinishE` and proves equality with `finishUnrolledPolynomial` for every `Result` outcome. It then proves the corresponding `FinishOps` record is equal, so the actual extracted `finish_relation` call is unchanged except that its polynomial implementation is the original-body adapter. `s2_original_polynomial_success_equations` reuses the checked finish success inversion and exports the existing numeric round equations and output equalities under this original-body operation. It introduces no new numeric or source-unroll premise.

The proof excludes generated Funs/FunsExternal/TypesExternal stubs. Direct imported owners are pinned by `attempt/proof-evidence/preflight.json`: `AeneasOriginalPolynomialBodyAdapterV1` object `a8cf7e2c…` and `CurrentFinishCandidateUnrolledPolynomialV4` object `58d5364c…`. Their exact source, receipts, and transitive evidence packets are referenced/copied in `dependencies/`; no compiled object is included.

NUC focused proof: Lean 4.32.0 `-j1 -M 4400`, MemoryHigh 1GiB, MemoryMax 2GiB, MemorySwapMax 0. Exit 0, wall 2.607s, peak process RSS 3,689,812 KiB, cgroup peak 367,915,008 bytes, swap 0, no memory events. All three printed theorem axiom sets are `[propext, Classical.choice, Quot.sound]`.

Open boundary remains Rust core `Range<usize>::rev().fold` to the selected emitted Aeneas operational `Rev.next` loop. The packet does not claim adoption of the explicit-unroll source candidate.
