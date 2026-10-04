# R608 circle outcome events

R608 proves exact correspondences for the pure selected circle-parameter policy. An accepted output is a circle point precisely when its decoded QM31 value is the point's parameter and has nonzero imaginary part. A rejected output (`accept = none`) is precisely a decoded value with zero imaginary part. It also counts the rejected canonical four-limb tuples as `modulus^2` and proves that `R607FieldSetMass.setEvent` for that set is exactly the event that the policy rejects the output.

The target is [`R608CircleOutcomeEvents.lean`](lean/AspisV8R19/R608CircleOutcomeEvents.lean), namespace `AspisV8R19.R608CircleOutcomeEvents`. It defines the rejected tuples via the two zero final coordinates and proves that predicate is equivalent to zero imaginary part. The event lemma is factored through a general membership-to-image result, so it does not normalize the large concrete finite tuple universe.

The final source is byte-identical to the reviewed green snapshot, SHA256 `3d0783a2fa333b4d64a05c085ccaf587cf433bc347f9236a98ecd71de31a37c3`, at source revision `e370c116ce66eac8b2cd114dd4c3f35bb5bb3983`. The focused Lean target compiled successfully with exit status 0 in 1.52 seconds, peak Lean-child RSS 3,271,740 KiB, and swap 0. It ran in the pinned cached Lean 4.32 workspace with `-j1 -M4500`, under a systemd user scope capped at `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

Complete `#print axioms` output:

```text
'AspisV8R19.R608CircleOutcomeEvents.accept_point_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R608CircleOutcomeEvents.accept_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R608CircleOutcomeEvents.rejected_tuple_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R608CircleOutcomeEvents.rejected_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This closes only the pure tuple-decode and parameter-policy event boundary. It does not establish the actual shared-oracle challenge law, the complete three-attempt sampler distribution, adaptive retry losses, or a privacy/security conclusion. The next missing proposition is the complete selected sampler's three-attempt outcome law under a single shared oracle, including fresh-address/history conditions and the retry stopping behavior.

All 25 focused R608 attempts, including failed proof iterations, their exact source snapshots, logs, and receipts are preserved in [`evidence/r608-circle-outcome-events`](evidence/r608-circle-outcome-events/). The final receipt also records direct-import source hashes, runner hash, cache resource caps, and measurements.
