# R602 circle parameter count

R602 gives a symbolic count for four independently chosen `Fin p` coordinates, with `p>0`: the number of tuples whose last two coordinates are not both zero is `p^4-p^2`. The complement has its last two coordinates fixed to the explicit `Fin p` zero and its first two coordinates arbitrary; the equivalence in the proof establishes that its size is `p^2`. The theorem also specializes the count to the selected M31 modulus.

The source is [R602CircleParameterCount.lean](lean/AspisV8R19/R602CircleParameterCount.lean), SHA256 `a354ecfc2ec5ad236a34b4472dabb01467bd6f9e0f8a8e8d129a42e514a89d8c`, source revision `e23f6e2008c98c5d8d0139fe4d967d97b7f1ea64`. It imports `R445InitialBlockRejectionLaw.lean` (SHA256 `efe55338ba9bc5a7ccf7c0383a431e1922ebaf80b7931b2798025eb8f4750d81`) only for the selected `modulus` alias.

The focused cached-workspace Lean check used `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Final attempt `1791092232720120000` exited 0 in 1.85 seconds, with peak Lean-child RSS 3,270,448 KiB and swap 0. Complete axiom output:

```text
'AspisV8R19.R602CircleParameterCount.fixedTailEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R602CircleParameterCount.circle_parameter_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R602CircleParameterCount.selected_circle_parameter_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All five attempts and their exact source snapshots, logs, and receipts are retained under [evidence/r602-circle-parameter-count](evidence/r602-circle-parameter-count/). The earlier proof errors and final clean result are both recorded.

This is only a finite counting identity. It does not connect this set to actual sampler acceptance, establish an output law, or assign a probability to sampled circle parameters.
