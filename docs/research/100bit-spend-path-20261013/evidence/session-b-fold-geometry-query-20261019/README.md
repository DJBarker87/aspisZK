# Focused extractor proofs: R17 fold arithmetic and QueryScan v15

This packet contains exact source snapshots, source pins, Lean logs, preflight data, commands, and receipts. It intentionally does not include `.olean` binaries. The accepted targets were checked with Lean 4.32.0 in NUC systemd scopes, with `MemorySwapMax=0`.

## Accepted results

- `R1ZCircleFoldMathV1` proves the deployed `circle_fold` and `line_fold` arithmetic equal the corresponding formal fold expressions. The line-fold proof records the deployed sign convention: the second line-coordinate input is `-half * iy`.
- `R1ZQueryGeometryValuesV6` proves `line_node` equals the stored first-line coordinate, identifies the three line-derived denominators in `QueryGeometry`, identifies their pointwise inverse contributions, and composes those values with the formal line-fold expression.
- `QueryScanBlockRankCallbackExact` v15 checks the prior accepted callback target after removing its `maxHeartbeats` override. Its exact source differs from v14 only by removal of that option override.

All declarations audited in the accepted logs report only `[propext, Classical.choice, Quot.sound]`; no accepted target reports `sorryAx`.

## Source boundary and remaining work

The Rust source snapshot is `source-pins/verifier.rs`, SHA256 `93f36867c92f6f32434cc9e11090e573cb838bce362dc0ace8142ffcbc48fc41`. Relevant spans are `circle_fold` lines 154–162, `line_fold` lines 163–178, `QueryGeometry` and `for_range` lines 180–216, and the inverse-consuming fold functions lines 218–236.

The geometry theorem uses the mathematical pointwise inverse vector corresponding to the five denominators. It does not yet prove that `QueryGeometry::for_range`'s prefix-product/backward-pass implementation returns that vector. The `fibre_point` output-to-stored-point adapter and whole source caller refinement remain open. The QueryScan target is a separate accepted proof and does not close those geometry/source-refinement obligations.

The v1–v5 geometry attempts are preserved in their original NUC attempt directories; this packet carries the final changed source and green v6 receipt only. The changed proof was prompted by concrete tactic diagnostics; no memory cap or option override was increased.

## Reproducibility

Each `evidence/<target>/preflight.json` records direct import hashes, source hash/revision, Lean binary hash, import path, and scope limits. Each receipt records exit, wall time, process RSS, cgroup peak, swap, object hash, and source hash. Commands and complete Lean output are next to each receipt. `SHA256SUMS` covers all packet files except itself.

Publication addendum: the five listed fold/QueryGeometry Rust items are byte-identical to the adopted c8ea8dd49 source; exact ranges and hashes are in source-pins/adopted-expression-continuity.json. The whole Rust-file snapshot differs outside those items. The QueryScan theorem retains the explicit model-backed from_fn correspondence boundary documented in the predecessor packet. No broader source refinement is claimed. The original worker manifest is preserved separately; the publication manifest uses the common modules/receipts schema.
