# Terminal reachable `from_fn` replacement candidate v4

This is an isolated source candidate based on current `research` HEAD `2f816c0f1e146f002afba58170e378b739945966.` It replaces the 19 `core::array::from_fn` calls in the default-feature path from `Public::terminal_qm31` through `composition_parts`, `semantic_packed`, the projected state-only Poseidon evaluator, and the called lazy Poseidon row/limb helpers. The shared helper remains private to `aspis-statement`. The exact patch and full changed source snapshots are included.

A capped actual Cargo type check passed for the real `aspis-statement` and `aspis-core` packages with `r0,pool-v1-kernel` enabled, plus the three path writer packages. It took 16.503 s with sampled aggregate RSS 396,247,040 bytes under a 7 GiB / 120 s watchdog. This validates actual crate-root visibility and real QM31/u64 type checking; it does not validate Aeneas output or callback arithmetic correspondence.

The existing claims-selector, `composition_parts`, external-sum, internal-loop, and projected-evaluator proofs are pinned in the manifest as candidate support. They were proved against earlier generated shapes and have not yet been rebound to the v4 extraction. The v4 source keeps callbacks pure and invokes them in ascending index order, matching the indexed helper shape.

Remaining `from_fn` calls are in test-only or audit-only code and the host-only opening constructor, which is not called by the terminal verifier path. Their source classification is in the manifest. Other reachable external templates (array map, iterator/fold, Result map/map_err, and U16 bit-count operations) still remain, so this candidate alone does not close the external-template axiom.

The next verification is a capped Aeneas extraction of this exact packet, using the pinned warmed workspace and preserving the existing tuple-only metadata adapter. It must confirm the generated declaration corresponds to the v4 sources; do not reuse historical v10 generated Funs as though they represented this candidate.
