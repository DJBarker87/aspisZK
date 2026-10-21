# Row-aware oracle-port draft, 2026-10-21

Branch `codex/cx-rowaware-draft-20261021`, base `b81ae0928`.
This is an unmerged draft based on the unapproved oracle-port draft. No
production or existing Lean module is modified.

## Causal refinement

`OraclePortRowAwareCausalD1` specifies a table-only causal gate. A witness
starts at a tag-2 initial message, recursively caches every query in each
preceding sampler row, and provides recognition of that row's first cell
in a subtable of the current table. An absorb cannot pass merely by being
parseable in isolation. The witness uses the actual 33-row sampler schedule,
including reseed and query rows. The gate is a noncomputable specification,
not an executable parser or a source refinement.

The decoder filters `RecordedBinaryExperimentBin.dec`, preserving its whole
background computation and output function whenever the gate passes.
`decode_some`, `retained_value`, and `density` prove this and retain the
existing classifier budget. These are retained-start results, not yet
accepted-run completion or equality of the complete extractor.

## Verification

Focused local compiles use the required 4.32.0 toolchain and
`-j1 -M4400 -DElab.async=false`, shared mkdir lock, and private objects.
Per-attempt source snapshots, exact commands, revision, hashes, dependency
fingerprint, exit, wall time, peak RSS, swaps and axiom output are in
`../evidence/rowaware-draft-20261021/manifest.json` and attempt directories.
The first two attempts failed on a missing namespace for `Table`; the
resulting elaboration diagnostics are not accepted proof evidence. Attempt
3 passes all four axiom audits with standard axioms and zero swaps.

## Outstanding investigation

Causality alone may not exclude the frozen node overlap: the existing
witness already walks from initialisation through row zero. A counterexample
against the stronger full-row gate is being checked. No Q+34 or premise
removal is claimed at this stage.
