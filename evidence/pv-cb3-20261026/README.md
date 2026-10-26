# PV CB3 callback source equations

Branch `codex/pv-cb3-20261026`, independent callback rows of recount 2.
Prefix `PV_CB3_`; Env J 24700–24999; budgets 100 Lean / 20 Kani.

The current checked row table is `ROWS.md`; op246/V254, op229/V246, op225/V242 and op120/V219 are
discharged on this candidate by their `PV_CB3_Op*Source.op*_source` theorems,
receipts 24701, 24705, 24711 and 24754. Recount 2 baseline:
OPEN 110, independent OPEN 51, CLOSED-ON-CANDIDATE 40; adding this worker gives
106 / 47 / 44. Endpoint premises removed: 0.
Target not yet established.

The first four targets, descending: op258/V264, op253/V260,
op252/V259, op251/V258. `stage1-preparation.json` records the intended
complete Result law and input/feature caveats. Required sibling branch log and
source grep are retained separately for each op. Host snapshot copied only
into this worker's own directory; 782 tracked files match this worktree exactly
(`source-identity.json`). The sibling snapshot/cache were read only.

The initial two extraction preparations were self-held with exit 78 for the
announced 16:50–17:20 UTC window while the marker was absent. This was stricter
than ruling (e), and is corrected: only a live quiet-window marker or resource
reservation refusal prevents launch. Attempt 003 reached the actual reservation
scanner and was refused at 66.4 GiB reserved (8 GiB requested, 55 GiB safe limit).
No capped scope launched, no Lean/Kani attempt charged. Receipt:
`charon-source-op258-001/reservation-transport.log`. Retry after the required three-minute wait with a new extraction receipt
suffix; host launchers and reservation gates
remain authoritative. No shared infrastructure edited.

Collector metadata correction: the copied collector originally carried a legacy
821157fbdd source-identity phrase. It is replaced with this worker's verified
09df2340 base and the 782-file hash inventory; raw command/output evidence is unchanged.

P6 bindings for op51/op120: `P6-REFERENCE-PROVENANCE.json`; current no-stub native gates and named extracted-body SHA checks accompany both source equations. The retained-cache route is documented in `retained-cache-route.json`.

Final review withdrew op51 credit: its Kani harness canonicalizes through WideExact::new, so the complete arbitrary-carrier source correspondence is still OPEN. The checked selected-to-reference equation remains supporting evidence. See P6-REFERENCE-PROVENANCE.json.
