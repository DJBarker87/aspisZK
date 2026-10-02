# R295 signature failure source inventory

Read-only inventory for the R295 Aeneas error. Input is the exact R294 LLBC copy from R295: SHA-256 `bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f`, `has_errors=false`.

The Aeneas assertion at `SymbolicToPureTypes.ml:1047` checks that `sg.item_binder_params.trait_type_constraints` is empty. The source span on the diagnostic maps exactly to LLBC `Fun 58`, `core::iter::traits::iterator::Iterator::try_fold`, `iterator.rs:2486:4–2490:35`; its `src` is `TraitDecl { trait_ref: Iterator, item_id: Method 36 }`. Fun58 is `Foreign`/`Opaque` in this LLBC, but its signature metadata is present.

Fun58 generic binder names are `Self, B, F, R, Clause0_Item` (plus one unknown-mutability region binder). Its signature is `(&mut Self, B, F) -> R`. The encoded trait clauses include `Iterator<Self, Item>`, `FnMut<F, (B, Item), R>`, `Destruct<F>`, and `Try<R>`. The single binder `trait_type_constraints` entry has trait ref `Clause.Free(3)` to `Try<R>`, associated `type_id=0` (Try's `Output`), and target type `B`. Hash-cons IDs 8977/8978/8984/9035 decode to free type variables 0/1/2/3 respectively (`Self/B/F/R`).

Related declaration `Fun 120`, the transparent selected `Chain::try_fold` implementation in `chain.rs:99–103`, has a parallel `Try<R>` constraint with associated `Try::Output = Acc`. This is a separate declaration and source span; it is recorded for context, not asserted as the source of the observed first error.

Saved files include byte-for-byte copies of pinned `SymbolicToPureTypes.ml` and nightly-2026-06-01 `iterator.rs`, focused numbered excerpts, their SHA-256 hashes, and the decoded rows in `inventory.json`. No declaration, signature, source, or translator behavior was edited, and no build or extraction was run for this inventory.
