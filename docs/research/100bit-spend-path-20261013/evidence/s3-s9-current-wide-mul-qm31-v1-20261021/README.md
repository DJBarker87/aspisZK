# Current WideExact `mul_qm31` model

This packet records a green Lean proof of the source-shaped `mul_qm31` operation model and its canonical-output/decoded-product theorem. It is a focused semantic model result, not a proof that the retained Lean function is the translation of the Rust method.

The Rust method is pinned at `crates/aspis-core/src/field/wide_exact.rs` (SHA-256 recorded in `manifest.json`): `WideExact::mul_qm31` canonicalizes the four right-hand QM31 limbs and then calls `QM31::mul` for `c0` and `c1`. The Lean model follows that operation order. The outstanding boundary is an exact source/generated-body correspondence and installation into the helper's `wideMulQM31` operation slot. The other field-operation slots and enclosing `Weights::pair` caller remain open.

The successful NUC compile used Lean 4.32, `-j1 -M 4400`, in a systemd scope with `MemoryHigh=1 GiB`, `MemoryMax=2 GiB`, and `MemorySwapMax=0`. The compiler log reports standard axioms only: `propext`, `Classical.choice`, and `Quot.sound`. The process RSS includes shared mappings; scoped peak and swap are recorded separately in the receipt.

The runner preflight contains a configured source revision, but that value was not captured at process launch. Because the repository HEAD advanced concurrently, the actual launch Git revision is recorded as unknown here rather than inferred. No binary object is included in this source-only packet.
