# R136 verified evidence

- Direct selected-callback extraction: PASS.
- Aeneas translation: PASS.
- `TwoSwapResidualPolynomial.assigned_eq_source_matrix`: PASS.
- Generated `before_ood` external implementation layer: OPEN.
- Exact Rust-to-run equality through `before_ood`: OPEN.
- Actual selected sampler/admissibility law: OPEN.
- Full privacy: not claimed.
- Full soundness: not claimed.

The frozen callback and its `aspis-core` field/transcript dependencies are
copied under `source/` and pinned by SHA-256.  `r18-stage.json` pins the wider
selected source stage.
