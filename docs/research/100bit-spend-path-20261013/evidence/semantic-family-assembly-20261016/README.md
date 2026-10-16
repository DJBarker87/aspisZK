# Occupancy source correspondence and full semantic packing assembly

`OccupancyCompletePacking.boxed_add_occupancy_lanes_success` completes the occupancy family at the same actual boxed point. It derives canonical high/low selectors, matches actual selector row outputs by uniqueness of successful source results, and applies the complete generated occupancy caller. Its packed output contribution equals the retained occupancy family after the existing field embedding. The family is kept behind `wideOccupancyFamily` to prevent concrete-field normalization; `wideOccupancyFamily_residuals_eq` proves exact equality to R0P.occupancyFamily. No operation success, row value or residual identity is assumed.

`SemanticPackedIntervalAssembly.pack_intervals` proves the full source-order sum of six family contributions forms the intended scalar slots: schedule 0–31, path 32–48, value 49–83, digest 84–91 and asset 92–93, with occupancy added at 0–11. Values at 94 and beyond are zero. The proof uses symbolic list bounds and the existing generic pack4 addition theorem, without reducing concrete field expressions.

`SemanticPackedFamilyAssembly.packed_family_contributions` discharges all six list lengths and identifies the assembled output with the existing arbitrary-point R0P.SemSource.scalarLaneAt. This reuses the lane map already consumed by the retained terminal soundness and degree theorems. It is the algebraic assembly bridge; it does not itself prove execution of the whole generated semantic_packed caller. The public-digest outer source loop/wrapper and that whole-caller composition remain open, along with admitted caller/transcript/custody and release-artifact correspondence, accepted-spend soundness and privacy.

All focused targets exited 0 on the capped NUC, with zero process swaps and standard-only theorem axioms. Exact targets, source revisions and hashes, object/import pins, commands, reservations, wall time, peak RSS, swap and axiom reports are retained. The interval module was checked under its actual top-level import name; an earlier equivalent check under a dotted module name is not substituted for the correct consumer pin. No broad replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `OccupancyCompletePacking` | 5.225 | 4006356 | 3 |
| `SemanticPackedIntervalAssembly` | 2.092 | 3995404 | 3 |
| `SemanticPackedFamilyAssembly` | 1.621 | 3983848 | 3 |
