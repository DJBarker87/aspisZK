# V7 fresh-history projection alignment

`lean/FSV8V7HistoryProjectionAlignment.lean` constructs the current FS state
as `projectOracleState` of a V7 fresh-only oracle prehistory. It proves
history-total coherence and no-programmed preservation by query/run induction,
and reuses V7's exact fresh-count, consumed-prefix, and finite-tape bounds.

The promoted endpoint `uniform_run_projected_state_aligned` removes the
caller-supplied projected prefix for the ideal `runMachineFromUniformFreshTape`
execution from `emptyOracle`. It chooses `extendFreshTape finiteTape fallback`,
proves the projection identity, and derives the range-map prefix internally.

This does not couple an arbitrary adversarial prehistory, deployed ROM, or
source execution to the V7 tape law. Such a coupling still requires a
history-producing adversary/distribution premise. No probability or
independence claim is made here.

Evidence: pinned Lean 4.32.0 NUC compile, `-j1 -M8192`, exit 0, wall 2.92 s,
maximum RSS 6,538,096 KiB, swap 0. Source SHA256
`4e138bbcfd2aed079036edb1cd758f2cd6c75664c248e389781d74714aa7061d`; OLean
SHA256 `3e0505957782216a9bfa4a99b4709ca975fc884d9a9d242af83345bcd9762`.
The final endpoint reports `[propext, Quot.sound]`.
