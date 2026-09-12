# Replayable source collector adapter — 2026-09-12

`lean/FSV8ReplayableSourceCollectorAdapter.lean` adds the smallest
source-facing causal adapter. `bindMachine` runs an arbitrary
`OracleMachine Observation`; only its returned observation constructs the
compiled replayable source/OOD/gamma/middle/later continuation. Abort remains
an oracle abort and is not converted into a returned record.

`bindReplayableOrigin` closes this dependent machine into the existing V7
`SameTapeExperimentOrigin`, and `bindReplayableSourceAttempt` feeds that
origin directly to the existing `sourceAttempt`/fork collector. Thus the
caller no longer supplies a body/observation to the verifier continuation;
the body is selected by the preprogram's returned observation. Existing V7
legal-replay, programming, fork, and resource classifications remain visible.

The remaining seam is genuine: the actual Rust/Aeneas adversary capability
must be represented by `preProgram`, and the configured V7 programmed target,
hash/transcript driving input, fork scheduler, and resource premises still
need an instantiation. No ROM coupling, acceptance, independence, or
successful-fork claim is made.

Evidence: `results/replayable-source-collector-adapter-v1/report.json`.
