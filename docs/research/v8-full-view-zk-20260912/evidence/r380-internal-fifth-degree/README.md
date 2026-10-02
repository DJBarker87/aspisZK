# R380 internal fifth-power degree lemma

Status: byte-identity promotion and evidence archive prepared; uncommitted. The original root-relative run is preserved. A later byte-identical compile used the module-qualified target path because the corresponding qualified cache artifact was missing; that cache/path mismatch was the explicit reason for this second run.

The promoted module `lean/AspisV8R19/R380InternalFifthDegree.lean` is byte-identical to `promoted-source/R380InternalFifthDegree.lean` (SHA-256 `53c6cb1004dab30d35a02f5f0b9292bd71d054b27c6c377e770e384fb69b54b7`). It imports `AspisV8R19.R378PairedFifthDegree.lean`, SHA-256 `6cb2cfc099d5722cacc04fe604c19ee67f5e079bd3eab2f8bcf9fdf239f1e810`; a copy is included under `source-route/promoted-imports/`.

The two proved polynomial statements are `internalRound_degree` and `two_internalRounds_degree`. The module defines the specified conditional fifth-power map and uses the existing generic linear-layer degree result. Its proof handles active and inactive coordinates separately. Both complete `#print axioms` reports are `[propext, Classical.choice, Quot.sound]`.

Lead review accepted the definition and degree composition, including the inactive case bound `d ≤ 5*d`. This establishes a generic polynomial lemma only. It does not bind the map to selected Rust execution or close a terminal degree proof. The first remaining proposition is to bind the selected `internal_round` implementation, including its active lane 0, linear layer, and constants, to the generic polynomial model. Packing occurs downstream, after `interpolated_internal_pair`; it is not part of the `internal_round` helper itself. The next step after that binding is the complete projected-terminal degree argument.

## Focused run

The original focused run `1790952289292760000` compiled the file via root-relative target `R380InternalFifthDegree.lean`: exit 0, wall 0.96 s, GNU-time Lean-child maximum RSS 2,290,952 KiB, swap 0, revision `d399ad195e115a33bd1e06478bb4627172d6f34e`. Root later found that only the root-level olean existed while the qualified `AspisV8R19/R380InternalFifthDegree.olean` required by the import path was absent. To establish that exact cache artifact, the same byte-identical module was compiled once as `AspisV8R19/R380InternalFifthDegree.lean` in run `1790952545664319000`: exit 0, wall 0.89 s, GNU-time Lean-child maximum RSS 2,291,396 KiB, swap 0, revision `9096682558907ed01cdb410291c02a45ab8edd56`. Both used the pinned runner (copy in `runner/`), `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Both full axiom reports match exactly. The runner labels the Lean-child measurement separately from systemd wrapper peak.

`verify_evidence.py` performs read-only checks for all bundle checksums, promoted-source byte identity, exact imported-source hash, both saved run input/log/receipt identities, cap/metrics/status, and both requested axiom reports. No further rerun is included.
