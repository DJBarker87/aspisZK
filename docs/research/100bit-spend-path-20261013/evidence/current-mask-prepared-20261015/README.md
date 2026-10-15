# Current extracted prepared-multiplier evidence

Fourteen focused Lean targets pass with 46 axiom reports, all limited to
`propext`, `Classical.choice`, and `Quot.sound`. The final theorem
`ExtractedMaskPreparedMul.current_prepared_correct` derives the stored-state
invariant from the actual extracted constructor and proves a successful,
canonical result whose exact-field decoding is the input product. Canonical
input premises are explicit. This is a theorem about the pinned extracted
helpers, not complete Rust-verifier acceptance or private-spend soundness.

The bundle reuses six historical pure modules unchanged and retargets nine
already-checked current arithmetic modules by exactly two namespace/module
substitutions. The maintained adapters and snapshots match the final receipts.
The archive retains sources, target objects, emitted object companions, direct
import pins, commands, raw logs, axiom reports, failed attempts, and both reuse
inventories. It relies on the recorded external Lean/Aeneas/Mathlib cache; it
is not a standalone full dependency distribution. The generated Types/Funs
checks are included as prior dependencies and are not counted among the 14
new theorem targets.

All successful targets used Lean 4.31.0 locally with the existing cached
libraries, `-M3000`, a 4 GiB sampled process-group stop, and a 300-second limit.
The largest successful sampled aggregate RSS was 3,099,264 KiB; successful
process swap counts were zero. There was no cold dependency or full-manifest
rebuild. Exact per-target time, revision and resource results are in the
manifest; the final multiplier module took 12.393 seconds.

## Preserved failures and replacement

`mask-reducer-a` failed because the reused RawReducerNat cache lacked emitted
companion files. Copying and hash-checking the pinned companions fixed it;
`mask-reducer-b` passed without changing its source or rebuilding dependencies.

Component attempts a/b failed in unfolding/simplification. Attempt c had an
underconstrained term and heartbeat errors. Attempt d reached the 3,000 MB
Lean memory limit during kernel reduction and exited 134. It was not rerun
with a larger cap. The replacement proves the generic symbolic closure
execution equation separately (`ExtractedMaskPreparedClosure.call_eq`), then
rewrites with that equation before the fixed array reads. Component-e and
PreparedMul-a passed under the same cap. Failed attempt diagnostics, including
any placeholder axioms printed after errors, are not counted as proof results.

## Scope still open

The canonical-input constructor/multiply contract does not yet prove the
selected-mask whole loop or its polynomial-model correspondence. Selected
linear forms, coefficient-array population, square/scalar helpers, terminal
evaluation and the actual Rust acceptance contract remain separate. The
extraction/compiler boundary, commitment compiler, efficient extraction,
privacy and complete admitted-runtime/settlement release gates remain open.
