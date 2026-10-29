# PV_DIAG10 — D468

**Target not yet established.** Worktree exactly `/Users/dominic/ZK/.worktrees/pv-diag`, sparse branch `codex/pv-diag10-20261029`, base `2d083b9a42`. Option B, complete observer and original error bound retained. T unchanged.

## Top-down acquisition skeletons

All three compiled within the first **six** Lean attempts (66703, 66704, 66705):

- `PV_DIAG10.DIAG_FILE_TRACE`: conclusion exactly `PV_RJ4IDB.OpenInputs.DIAG_FILE_TRACE actual native`.
- `PV_DIAG10.DIAG_JSON_STDOUT_TRACE`: conclusion exactly `PV_RJ4IDB.OpenInputs.DIAG_JSON_STDOUT_TRACE actual native`.
- `PV_DIAG10.DIAG_ERROR_STDERR_TRACE`: conclusion exactly `PV_RJ4IDB.OpenInputs.DIAG_ERROR_STDERR_TRACE actual native`.

Each takes four separate standalone Props: `PV_DIAG10_Link_Init`, `PV_DIAG10_Link_Step`, `PV_DIAG10_Link_Readout`, `PV_DIAG10_Link_EventOrder`. Init fixes only the empty-prefix accumulator; Step appends only one selected event; Readout relates the real channel to its source observer state; EventOrder relates the raw ordered source events to the NativeTrace events. None mentions an OpenInputs DIAG Prop or restates the final channel equality. `prefix_agreement` proves the recurrence invariant and uses the existing native projections; no channel decoder is duplicated. The same skeleton applies to every finite prefix of a divergent execution, arbitrary index types and all terminals.

These are conditional skeletons, not deployed instances. The actual source observer's initialization, single-step updates, readout and exhaustive event-order producer remain to be associated. Instantiating state with the desired projection alone would not discharge the deployed links. Acquisition and same-public independence are distinct: panic exclusion and option-B public laws can simplify honest source-step producers but cannot by themselves establish acquisition of actual bytes.

## Verification in progress

66700 rejected: missing List.reverseRecOn; replaced with accumulator induction (66701). 66702 rejected: append notation not definitionally closed by simp only; added explicit reflexivity (66703). Neither failed source was resubmitted unchanged. Audits reserved 66797–66799. Host caps 6G/8G, swap 0, TasksMax64, Lean -M7000; one scope at a time; admission requires exit 0 and allowed:true.
