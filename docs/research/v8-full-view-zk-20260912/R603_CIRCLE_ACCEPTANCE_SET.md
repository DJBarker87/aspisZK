# R603 circle acceptance set

R603 proves a deterministic policy characterization for every canonical tuple `x : Fin 4 → Fin P`. The exact field decoder has nonzero imaginary part precisely when either of the final two limbs is nonzero. The source-shaped `SamplerCirclePolicy.pureMap` succeeds for exactly those tuples. Consequently, the set of tuples accepted by that pure map has cardinality `P^4 − P^2`.

The source is [R603CircleAcceptanceSet.lean](lean/AspisV8R19/R603CircleAcceptanceSet.lean), SHA256 `f9a6d8199c95d0d8d42a55f5e84071e17e714c8f878d7f1277d236457ee8863e`, source revision `da33d1a953739cfcb43429fd564c295b463b5cf6`. Direct imports are pinned in the evidence manifest: R599 canonical tuple bridge, R602 symbolic count, and `SamplerCirclePolicy`.

The final focused Lean check used the pinned cached workspace, Lean `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Attempt `1791092941599686000` exited 0 in 1.29 seconds, with peak Lean-child RSS 3,265,092 KiB and swap 0. Complete axiom output:

```text
'AspisV8R19.R603CircleAcceptanceSet.fin_val_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R603CircleAcceptanceSet.tuple_im_nonzero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R603CircleAcceptanceSet.pureMap_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R603CircleAcceptanceSet.accepted_tuple_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six attempts, including failed proof scripts and their exact snapshots/logs/receipts, are preserved under [evidence/r603-circle-acceptance-set](evidence/r603-circle-acceptance-set/).

This theorem characterizes only the mathematical pure-map policy on a finite field tuple. It makes no claim about source refinement, source sampler acceptance, retry behavior, the adaptive oracle law, privacy, or soundness.
