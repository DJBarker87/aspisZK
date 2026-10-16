# Focused `echeck` source cut (preflight only)

This kit isolates the exact private helper `verifier.rs::echeck` from the current R1 cost-probe source. Its function declaration and body are copied byte-for-byte and checked by `extract_echeck.py`; only surrounding module wiring, the exact `Error` enum, and `echeck_round1(b)` reachability wrapper are included as scaffold. The field sources are copied unchanged from the same proof-worktree revision.

Pinned inputs:

- `crates/aspis-r1-cost-probe/src/verifier.rs` SHA-256: `b62d50ad47f9f4c736323f54e6d2b90e80fe18d4730d29994febe0ca0756734d`
- `crates/aspis-core/src/field.rs` SHA-256: `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`
- `crates/aspis-core/src/field/wide_exact.rs` SHA-256: `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b`
- `echeck` source lines 32–35; exact function slice SHA-256: `7048dc298b2770e6daad4f46dc16bbb4911e7c2cd87e9784c07b3173e713b3f8`

Intended proof target after translation: for `k = false`, a successful extracted `echeck` over a 224-byte `round1` slice entails successful ordinary `WideExact::from_le_bytes` on each of the seven 32-byte chunks. It does not include `View::parse`; the caller must separately provide the exact `round1` slice and length relation. That caller/cut theorem remains open. The package is named `aspis-r1-mask-extraction-probe`, matching the selected-mask extraction namespace `AspisR1SelectedMaskProbe`. This is intended to let the generated `field` declarations overlap with the retained selected-mask output; before Lean integration, compare those overlapping declarations byte-for-byte and retain only the new `verifier.echeck` declarations. The source module/caller linkage remains a separate proof obligation.

No Cargo, Charon, Aeneas, or Lean job has been run from this kit.
