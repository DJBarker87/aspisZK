# Privacy history split — 2026-10-21

Branch `codex/cx-priv-history-20261021`, base `d93756b49`.

## Stage 1: exact interface split

`QueryScanHistorySplit` separates the **actual** fields of `ScanCoupling`.
`ScanExecution` retains cp, eight coupling-space events and whole-observation
agreement off their union. `ProbabilityContent` is exactly the deleted mass
field. `exact_split` proves equivalence with their conjunction.

There is an obstruction to deleting the mass field with unconstrained events:
`vacuousExecution` supplies an execution join between any two observations
with coupled randomness by choosing all events True. `zero_one_no_scanCoupling`
proves that the constant Boolean observations 0 and 1 have no ScanCoupling.
Thus `probability_not_execution_content` is a compiled counterexample to
recovering that field from the literal execution-only remainder.

A sound interface must fix the events independently of the source join.
`ModelExecutionJoin source model bad` does so, with no probability fields.
Its `toScanCoupling` transports a separately proved model law via cp.meanM;
it does not assume independence between attempts or enumerate any carrier.
This is a usable separation, but it does not assert that the law has been
proved for actual ROM query failures.

Focused env J attempt 9801: exit 0, wall 2.14 s, peak RSS 3,517,108 KiB,
swaps 0; all five theorem audits use only propext, Classical.choice, Quot.sound.
Attempt 9800 retained a local rewrite elaboration failure, fixed by explicitly
instantiating cp.meanM at the event indicator. Complete source revisions,
SHA256, dependency fingerprints, launcher output and timing are in
`history-attempts-9800-9999.jsonl`. New sources/objects only; own drafts are
snapshotted under `snapshots/codex-cx-priv-history-20261021/<attempt>`.

## Stage 2: adaptive shared-oracle histories

Pending focused symbolic history check.

## Endpoint signature and before/after

Pending final statement audit. No unconditional replacement endpoint is claimed.
