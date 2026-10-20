# Stage2 prefix-to-prepared-alpha bridge

This packet records a focused, conditional bridge between the generated resume
reader prefix and the prepared-constructor suffix. The theorem
`successful_prefix_and_suffix_prepared_alpha` combines:

1. successful `resume_read_prefix` output, which supplies the two generated
   alpha values and their concrete reader-canonicality results; and
2. successful `resume_prepared_suffix` output called with those two values
   mapped field-by-field into the suffix's nominal field types.

It concludes that the returned `Prepared.alpha` is exactly the mapped pair and
retains canonicality of both prefix alpha values. These are separate success
premises. The theorem does not prove that the complete frozen `resume` body
reaches the suffix call, nor does it prove checkpoint/layout validation or
the other intervening reads.

The first combined-import attempt failed because both generated `Types`
owners declared the global `instDiscriminantErrorIsize`. The successful
attempt rebuilds the private suffix `Types`/`Funs`/field-inversion chain after
removing only the suffix `verifier.Error` discriminant annotation (the prefix
owner supplies that instance). The generated `Variant` annotation remains.
Generated resource-option lines were removed in the compiled copies as in the
prior suffix packet. The original generated sources are retained in
`../stage2-resume-prepared-suffix-20261020-v1/` and the exact compiled
transforms are included here. The suffix source expression is the frozen c8
return constructor recorded in `source-cut-check.json`.

The exact Lean command was Lean 4.32.0, `-M4400 -j1`, under a NUC cgroup with
`MemoryHigh=512 MiB`, `MemoryMax=2 GiB`, and `MemorySwapMax=0`. The GREEN
receipt reports exit 0, 1.402 s wall, peak process RSS 2,381,316 KiB, process
swaps 0, cgroup peak 291,549,184 bytes, cgroup swap 0, and no memory events.
The axiom report is `[propext, Classical.choice, Quot.sound]`. See
`native/bridge-v3/receipt.json`, its `time.log`, and the admission and
reservation records.

The failed duplicate-instance attempt is preserved under
`native/bridge-v1-failed/`; it is not a proof result.

