# V7 C1 gamma canonicality

Source parent: `27b1b2d64`. Focused checks used Lean 4.32.0 on
`dombarker@100.108.41.90`, the existing compiled cache, and independent
`systemd-run --user --scope` jobs with `MemoryHigh=7G`, `MemoryMax=8G`,
`MemorySwapMax=0`. Each job invoked `check-r30-decoder-focused.sh` and thus
`lake env lean -j1 -R` for only its named target.

| Target | Source SHA-256 | Scope | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| `V7ProductionCallbacksR30MutableCanonical.lean` | `b0759c7311892aeb48efe5534afea5cf93726a2ab1a4b6c836dca53e2e46ba64` | `run-r8b912c80215d4ce79ce38dd7029bca11.scope` | 0 | 2.03 | 2,672,864 | 0 |
| `V7ProductionCallbacksR30GammaC1Canonical.lean` | `1991b718119851c63d07ac5f0f39b32a8e00c81b1135676c2227b2094a4be262` | `run-r8074b186b2004dad893946741e4dd5ab.scope` | 0 | 1.88 | 2,690,244 | 0 |

The mutable target audits `enumerate_some_all` and `enumerate_none_all`.
The C1 target audits `literal_c1_gamma_canonical` and
`callback_c1_gamma_canonical`. Every `#print axioms` result is exactly
`[propext, Classical.choice, Quot.sound]`.

C1 canonicality is established from the literal outer trace and the four final
wide reductions, followed by exact limb transport through the callback adapter.
The nested arithmetic accumulators are retained as successful source executions,
not normalized away or replaced with another algorithm. This proves output
canonicality; it does not assert exact gamma-combination semantics or prove
absence of arithmetic overflow.

The generic mutable predicate lemmas cover the adapter's slice replacements and
composed backward functions. Array reconstruction also covers its explicit
fallback, which returns the already canonical initial array.

The complete gamma query output still needs the helper contribution and packed
entry-point bridge. Normalized fold, terminal `runningCanonical`, and final
manifest replay remain outstanding. No full manifest was run.
