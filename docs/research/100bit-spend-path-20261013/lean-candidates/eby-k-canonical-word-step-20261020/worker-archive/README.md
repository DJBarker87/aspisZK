# Canonical-compatible EbyK actual fold bridge

This source-only packet repairs the reducer-owner mismatch in the earlier EbyK Dot fold candidate. The old packet's `R22CurrentReducerMul` object imports `ExtractedCurrentReducer` object `5d2a411b…`; the shared canonical closure uses object `16ed0514…`. The underlying `ExtractedCurrentReducer.lean` bytes are identical (`933ae275…`), but the object identities differ, so the old candidate is retained only as historical evidence and is not part of this selected proof chain.

The new `EbyKDotPushCanonicalFoldBridgeV1.fold_agrees` copies the exact `high`, `wrappingFold`, and `fold_agrees` declaration/proof block from the retained R22 source and imports the canonical reducer object directly. `checkers/check-packet.py` verifies the copied block byte-for-byte against the pinned R22 source snapshot and checks the exact canonical generated Funs/Types source hashes. The updated actual-fold consumer then proves the same `actualWrappingFold_value` and `actual_wrapping_fold_coordinate_step` results using that compatible bridge.

Accepted NUC targets:

- `EbyKDotPushNatStep`: source SHA `31a04306…`, object `763c0e48…`; receipt/preflight/log in `evidence/natstep-*`.
- `EbyKDotPushCanonicalFoldBridgeV1`: source SHA `33a6ed7e…`, object `e7b820cb…`; standard-only axiom report, receipt/preflight/log in `evidence/bridge-*`.
- `EbyKDotPushActualFoldV2`: source SHA `d2183e44…`, object `0dc40f90…`; both exported theorem reports are standard-only, receipt/preflight/log in `evidence/consumer-*`.

The NUC run used Lean 4.32 and a 1 GiB `MemoryHigh` / 2 GiB `MemoryMax` / zero-swap scope for each stage. Exact import paths and owners are recorded in the copied preflights and config. Canonical reducer source/object pins are `933ae275…` / `16ed0514…`. Canonical generated Funs and Types are the same source bytes as the earlier R22 snapshots (`114552b…`, `c5a084…`) but the coherent canonical OLean objects are `c38132cb…` and `9b621dc8…`.

This packet proves the fold primitive and one-coordinate accumulator residue step. It does not prove the whole `Dot::push` four-index loop or connect the raw products to QM31 multiplication. Those remain separate obligations. No OLean binaries are included.
