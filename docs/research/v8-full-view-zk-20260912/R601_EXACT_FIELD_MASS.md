# R601 exact field challenge mass

For every exact QM31 field value, R601 proves its ordinary-sampler success-event mass under the independent block-reply program law:

`((1 - (1/2147483648)^8) / 2147483647)^4`.

This is an unconditional target-event mass within that independent model, rather than a claim that the sampler never fails. The failed output remains `none`. The proof first identifies decoded-field equality with canonical four-limb tuple equality using R599, derives successful length from R600, and then applies R594 without changing retry budgets or challenge sizes. Zero field values are included.

Source: [R601ExactFieldMass.lean](lean/AspisV8R19/R601ExactFieldMass.lean), SHA256 `419f27cd81bdf57724fb66282643ddb5e5299e0aa92592da9ac4cb09b6746255`, source revision `bce59b682b9ca60ffb59e3a77477926f2b155b1c`. Exact target `AspisV8R19/R601ExactFieldMass.lean` compiled in the pinned Lean 4.32 cached workspace under `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, with `-j1 -M4500`. Final attempt `1791091738103136000` exited 0, wall `0:01.33`, peak Lean-child RSS `3267324` KiB, swap `0`.

Complete axiom output:

```text
'AspisV8R19.R601ExactFieldMass.canonical_field_event' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R601ExactFieldMass.block_field_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R601ExactFieldMass.source_independent_field_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three source snapshots, logs and receipts are saved in [evidence/r601-exact-field-mass](evidence/r601-exact-field-mass/). The first failed on missing namespace/type inference; the second on dependent rewriting of a decidable event; the changed final proof compiled successfully. No unchanged checks or CU benchmarks were repeated.

The first remaining proposition is a causal correspondence from the actual selected shared-oracle executions to this independent-reply law, with explicit losses for previously asked or colliding addresses, and then the complete circle/nonzero retry law. This theorem does not assert such correspondence, circle uniformity, a full published-view simulator, extraction, end-to-end privacy, or a 100-bit security bound.
