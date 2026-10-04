# R598: current native ordinary QM31 sampler correspondence

R598 proves that the captured native `Transcript.challenge_qm31` execution corresponds to the existing current-model QM31 challenge sampler. The proof follows the actual four-limb initialization, squeeze, outer retry loop, acceptance/exhaustion behavior, transcript return, and final limb-to-QM31 construction. Failure and divergence results are preserved. The successful outer-loop step uses the derived eight-word cursor bound; it does not assume cursor validity.

This is a focused execution correspondence, not an end-to-end privacy or security proof. It does not yet bind the nonzero wrapper, the full selected callback chronology, the shared oracle law, or the published-view simulator and probability loss.

The compile used the pinned Lean 4.32 cached workspace. Target: `AspisV8R19/R598NativeOrdinarySampler.lean`. Source revision recorded by the runner: `e370c116ce66eac8b2cd114dd4c3f35bb5bb3983`; exact source SHA-256: `9f0be3389c15c5ceda803a4ed766ac29ace8bfedf489931de062857dff982eca`. Exit status 0; wall time 2.17 s; peak Lean-child RSS 3,775,312 KiB; swap 0. The job ran in its own systemd scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, Lean flags `-j1 -M4500`.

The successful run is `1791095504412283000`. Its complete receipt and log, source snapshot, all earlier R598 failed and successful attempts, their receipts/logs/source snapshots, and a SHA-256 manifest are in [the R598 evidence directory](evidence/r598-native-ordinary-sampler/). The proof file is [R598NativeOrdinarySampler.lean](lean/AspisV8R19/R598NativeOrdinarySampler.lean). The four direct imported Lean sources are retained in the evidence directory and match the hashes in the successful receipt.

The full `#print axioms` output for the successful run is:

```text
'AspisV8R19.R598NativeOrdinarySampler.toCurrentTranscript' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.fromCurrentTranscript' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.toCurrent_fromCurrent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.nativeQM31' does not depend on any axioms
'AspisV8R19.R598NativeOrdinarySampler.nativeOutcome' does not depend on any axioms
'AspisV8R19.R598NativeOrdinarySampler.finishedNativeOuter' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.pendingNativeOuter' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.nativeControlOuter' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.currentInner_accepted_index_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
'AspisV8R19.R598NativeOrdinarySampler.outer_loop_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
'AspisV8R19.R598NativeOrdinarySampler.nativeInitialIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.nativeFinishChallenge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.nativeInitial_len' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.returnedChallenge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R598NativeOrdinarySampler.challenge_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
```

`core.fmt.Formatter` is an opaque standard-library **type** declaration in the pinned Aeneas source (`Aeneas/Std/Core/Fmt.lean`, SHA-256 `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`); it is not a proposition assumed by this proof. It enters through the existing inner sampler’s formatting-related result path. The R598 axioms report therefore includes that type constant, as well as Lean’s `propext`, `Classical.choice`, and `Quot.sound`.

The next missing sampler proposition is the actual selected `challenge_nonzero_qm31` wrapper correspondence, including its three attempts, stop condition, failures, and returned transcript. Even after that, the callback chronology and end-to-end privacy and soundness arguments remain open.
