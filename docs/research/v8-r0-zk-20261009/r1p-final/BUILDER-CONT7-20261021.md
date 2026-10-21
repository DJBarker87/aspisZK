# Builder continuation 7

Branch `codex/cx-builder-ref7-20261021`, base `b7a4cc502`.
No push or merge. Work and evidence are recorded incrementally.

## Stage 2: canonical Parts / column handoff

`BuilderPartsContent.canonical_merge_cell` proves raw canonical split/merge
preserves every copyCell for arbitrary records, with no WitnessOk or PubCorr
assumption. `cell_eq` transports componentwise block/path/aux correspondence
to the actual Parts dispatcher. `banks_columns` composes that transport with
the actual full-bank materialization and column-major readout, including
thirteen zero padding columns. The proof is symbolic; no cell enumeration.

This is a conditional callee handoff: `Content.blocks`, `.path`, and `.aux`
are still required. It does not prove actual Parts computes canonical
components, and `columnCell` is mathematical readout, not extraction of the
shipped Vec wrapper. Neither qualification is a released source join.

Env J 9308: target `R1Z.BuilderPartsContent`, exit 0, wall 2.75 s,
peak RSS 4,006,804 KiB, zero swaps. All three #print axioms audits use only
propext, Classical.choice, Quot.sound. Exact source/dependency fingerprint,
revision and complete logs: `builder-cont7-attempts.jsonl`. New module;
no shared source/object replaced. Compiled with the task-owned run-joint.sh,
-M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.

## Stage 1: nullifier owned route

In progress. Pending Kani/extraction results must not be treated as certificates.

## Stages 3–4: runtime and execution

Pending. The inherited endpoint's runtime and execution joins remain explicit.
