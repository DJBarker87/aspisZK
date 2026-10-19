# Raw semantic finish and operation evidence

This focused bundle records green Lean targets for finish checking, generic polynomial identities, an array adapter, and the latest extracted arithmetic-probe QM31 boundary/Horner refinement. It is evidence for these exact source snapshots only, not a unified release manifest.

`RawExtractedSemanticQM31Ops` v7 supersedes the earlier v3/v4/v6 green snapshots and includes Result-fold refinement for the selected arithmetic-probe QM31 add/mul operations, fixed-array boundary evaluation, and reverse Horner evaluation. Its direct machine owner is `ExtractedMaskQM31Exact`. It does not identify `RoundModel.Boundaries` with these folds or establish a type/operation bridge to production `aspis_core::QM31`.

The finish theorem remains at the abstract checked-round model. The generic polynomial and array lemmas remain algebraic identities. The Rust `r1_semantic.rs` source is explicitly labeled `UNPROVED COST PROBE`; nothing here claims production extraction or verifier acceptance. The CU-savings candidate report says `r1_semantic.rs` is unchanged while `factored_s2_libra_weights` and `Weights::pair` changed and still require formal re-pinning.

See `manifest.json` for exact source/object hashes, commands, direct imports, compiler/source revisions, exit status, wall time, peak RSS, swap, and axioms. `green/` contains the selected green snapshots; `diagnostics/` retains failed attempts and prior green revisions. OLean binaries are not included.
