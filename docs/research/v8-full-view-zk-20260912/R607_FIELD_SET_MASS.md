# R607 complete finite field-set mass

R607 extends the individual target-value law to every finite subset of canonical four-coordinate tuples. Under the independent-reply law of the existing source-shaped ordinary challenge program, the probability that the decoded output lies in the field image of a tuple set `S` is exactly

`S.card * ((1 - (1/2147483648)^8) / 2147483647)^4`.

The proof establishes a pointwise partition of the set event into disjoint exact field-target events using R599's bijection, proves finite-sum linearity of `outputMean`, then applies R601. It retains `none` failures with event value zero. No sampler success conditioning, shape assumption on arbitrary observed lists, independence between actual repeated oracle addresses, or private witness premise is added.

Exact target `AspisV8R19/R607FieldSetMass.lean`; source [R607FieldSetMass.lean](lean/AspisV8R19/R607FieldSetMass.lean), SHA256 `a99f02a18942eab7b6b4a048fee0f30ea8d3551ec24d0e049f4cd7a98daa8423`, source revision `da33d1a953739cfcb43429fd564c295b463b5cf6`. Final attempt `1791092960450723000` exited 0, wall `0:01.34`, peak Lean-child RSS `3269704` KiB, swap `0`. Pinned Lean 4.32 cache, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.

Complete axiom output:

```text
'AspisV8R19.R607FieldSetMass.set_event_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R607FieldSetMass.mean_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R607FieldSetMass.outputMean_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R607FieldSetMass.source_independent_set_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exact source snapshots, logs, receipts, direct imports and runner are saved in [evidence/r607-field-set-mass](evidence/r607-field-set-mass/). The first failed attempt made a simp cycle between `sum_const` and `card_eq_sum_ones`; the final proof removes the reverse rewrite. No resource cap was raised and no unchanged check was repeated.

The first remaining proposition is the complete circle/nonzero accepted, rejected and stopped outcome distribution, followed by a bound on the actual cached-oracle distance and binding through the full callback. Universal joint mask compatibility, published-view simulation, soundness extraction and overall security accounting remain open. R607 is not an end-to-end privacy/security theorem.
