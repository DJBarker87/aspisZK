# V7 packed gamma canonicality

Source parent: `009fb254f`. Focused Lean 4.32.0 checks ran on
`dombarker@100.108.41.90` with the existing R26/R29/R30 cache. Each target used
`check-r30-decoder-focused.sh` (`lake env lean -j1 -R`) inside its own
`systemd-run --user --scope` with `MemoryHigh=7G`, `MemoryMax=8G`,
`MemorySwapMax=0`.

| Target | Source SHA-256 | Scope | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| `V7ProductionCallbacksR30GammaHelpersCanonical.lean` | `aeadbbbd3290502f246787a76923789e3cdbf42d663823834e60ba85c42c8190` | `run-r8cd670f66c044207a0ea48c9844b18f9.scope` | 0 | 2.02 | 2,689,136 | 0 |
| `V7ProductionCallbacksR30PackedGammaCanonical.lean` | `74678685d9047c5fc6c75b298e5ceec2b34c576dbaaa0e9312635148f03b23fc` | `run-rb752d59719aa452885083c5838449d37.scope` | 0 | 1.81 | 2,685,620 | 0 |

Axioms audits for `successful_gamma_final_loop_canonical`,
`successful_helper_population_canonical`, and
`successful_packed_gamma_canonical` all report exactly
`[propext, Classical.choice, Quot.sound]`.

The packed entry theorem requires only the literal source call to return
`ok (.Ok output)`. It proves all four returned QM31 values canonical and retains
the successful source decoder equations and canonicality certificates for both
104-limb C1 and 48-limb C2 arrays. The helper contribution follows exact mutable
loop traces and the canonical Karatsuba reconstruction theorem. Its preprocessing
executions remain opaque successful equations; they are not concretely replayed.

This is a representation-invariant result, not a new claim of exact gamma
semantics or overflow freedom. The remaining chain is normalized fold output,
production query-batch output and the terminal `runningCanonical` premise.
No full manifest replay was run. One premature dependent check failed because
the helper module had not yet compiled; the helper induction was corrected and
then the dependent target was checked successfully.
