# R612 guarded circle law

Canonical target: `lean/AspisV8R19/R612GuardedCircleLaw.lean` (byte-identical to the compiled scratch source).

The pinned Lean 4.32 cached focus compiled the target successfully. Exit status: 0; wall time: 0:01.32; peak RSS: 3272936 KiB; swap: 0; source revision: `83cd1029d09ac9da85e19a989042c244d616e4ef`; source SHA-256: `730641a12d3a3561deed0d718a9251526230edd1ff4d20cb3b56b87b012f11ca`. Exact command, resource limits, full log, receipt, source snapshot, direct local dependency copies, and hashes are in `evidence/r612-guarded-circle-law/`.

The three theorems prove that the lazy memoized circle program's selected-point mass, outer `parameterExhausted` error mass, and inner `challengeExhausted` error mass each differ from their three-attempt independent-reply laws by at most `repeatLoss s cache`. They preserve arbitrary cache behavior; `repeatLoss` is not assumed numerically small.

All three `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]`.

This does not bind `repeatLoss` to the selected full callback's causal history, prove native circle execution or callback chronology through rho, establish a numerical security bound for the shared-oracle loss, construct a full published-view simulator, or prove privacy or soundness. The first remaining proposition is a concrete causal repeat-loss bound for the full selected oracle history.

Complete axiom output:

```text
'AspisV8R19.R612GuardedCircleLaw.cached_point_mass_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R612GuardedCircleLaw.cached_outer_error_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R612GuardedCircleLaw.cached_inner_error_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
```
