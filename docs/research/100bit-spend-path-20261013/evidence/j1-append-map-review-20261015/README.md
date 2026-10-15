# Independent artifact review: append-binding map

Reviewed `docs/research/100bit-spend-path-20261013/evidence/lean-append-binding-map-20261015` read-only against its own manifest, receipt-backed source snapshots, imported objects, and current local Lean sources. No Lean build was run.

The `5` receipt records are internally consistent with their exact source snapshots and sidecars; all `43` entries listed in the target `SHA256SUMS` verify. The deterministic object archive has `6` members and its digest/member hashes and sizes match the manifest. The three source files listed for target/refresh review match the current local files. All two failed `R1AppendBindingMap` attempts (a,b) remain present; the successful c compile, refreshed `R1SpendDataMap` append-a dependency compile, and `R1SpendRelationMap` append-a compile are recorded with exit 0.

The captured `R1SpendRelation` has `AppendBinding pub` in `Rspend`; `R1SpendDataMap` imports that relation snapshot and was recompiled; `R1SpendRelationMap` imports both `R1AppendBindingMap` and the refreshed `R1SpendDataMap` snapshot. The archive includes the corresponding pinned objects. This checks artifact and import bookkeeping only; it does not assess the theorem's security or source-refinement implications.

The detailed machine-readable checks are in `review.json`.
