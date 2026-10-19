# M10: polynomial bound for the actual Euclidean remainder ledger

This work is independent of the commitment-tree and proof-wire format. The existing actual long-division cost bound, raw remainder size theorem and value-preserving GCD mirror are reused; no commitment proof was continued after the lead's format hold.

`ActualRawModCostBound.raw_mod_cost_le` bounds the existing raw `%` mirror, including both normalization products, one abstract field inversion and its exact long-division coefficient-operation ledger. It proves

```
modBudget N = 100*N^3 + 800*N^2 + 1606*N + 5.
```

`ActualCompPolyGCDTotalRemainderCost.public_gcd_remainder_cost_uniform` carries the existing Euclidean size invariant through every fuel prefix. For canonical or noncanonical raw inputs whose array lengths are at most N, the full retained public GCD remainder ledger is at most

```
(2*N+1) * (100*N^3 + 800*N^2 + 1606*N + 5).
```

`CompPolyGCDRemainderBudget.gcdWithRemainderCost_value` lifts the mirror to exactly the canonical `CPolynomial.gcdMonic` called by the extractor. Its bound and a conditional per-field-operation bit charge are checked as well. `ActualScaledDivisorMonic` supplies the actual normalized divisor's trim, monicity and positive-length properties required by the retained division theorem. The two existing long-division cost model owners are proved equal, rather than silently substituted.

**M10 remains open.** This is a polynomial bound for the exact retained remainder ledger, not a complete runtime/bit-cost theorem for the GCD or extractor. Initial/recursive trims, terminal monic normalization, array representation/copy overhead, the concrete field's bit cost, and composition across the factorizer/RR/list/witness-checking call graph still need coverage. The new conditional beta charge does not establish beta for the field backend. No new failure probability, source acceptance refinement, or 100-bit deployment claim is made.

| Focused NUC target | Exit | Wall | Peak process RSS KiB | Cgroup peak bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| ActualScaledDivisorMonic | 0 | 1.806 s | 2,535,148 | 274,522,112 | 0 |
| ActualRawModCostBound | 0 | 2.209 s | 2,537,672 | 273,399,808 | 0 |
| ActualCompPolyGCDTotalRemainderCost | 0 | 1.505 s | 2,549,840 | 282,157,056 | 0 |
| CompPolyGCDRemainderBudget | 0 | 1.906 s | 2,531,152 | 271,425,536 | 0 |

All source-declared axiom reports contain only `propext`, `Classical.choice`, `Quot.sound` (some use fewer). There is no `sorryAx`. Exact targets, source revision `bc5902c79 +` the named changed target, source/object/compiler/import hashes, commands, time logs, preflight, admission and scope-registration records are retained. Each run used Lean 4.32.0, one thread, a 120-second watchdog, interpreter threshold 3200 MB, 512 MiB memory-high/1 GiB memory-max and zero cgroup swap. Existing polynomial/CompPoly caches were reused; no full manifest or package replay was run. The native mathlib revision matches the retained CompPoly cache's pinned revision.

The new working-set admission launcher is also retained in these kits. It permits independent capped jobs to overlap after recording a populated scope. It counts uncapped current memory minus only clean inactive file cache, adds swapped pages, keeps dirty/writeback pages, and retains the OS-growth reserve and aggregate reservation checks. The old gate had counted roughly 16.7 GiB of inactive file cache as unreclaimable usage despite more than 50 GiB available memory. The new admission records retain the raw snapshot and per-cgroup arithmetic. This removes that artificial serialization while keeping jobs individually capped; there is no time-of-day/fan scheduling hold.
