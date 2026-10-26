# Private env-J repair handoff

Branch: codex/pv-envfix-20261026. Research sources pinned at `3dbbe11f663278482e9382c451226c2c3fbc3ec8`;
worktree base `388253b6a8b94b31a6cd9b79faafffac01c2f5cc`. No proof source changes. Zero premises removed,
retained all existing endpoint/deployment obligations. Target not yet established.

## Measured diagnosis

See AUDIT.md, audit.json, effective_objects.json and the exact historical
source diffs. The two stale target variants explain the reported errors.
No strict R0Z/R1Z dependency hash mismatch; no missing strict dependency object.
No historical failed source will be retried unchanged. Rebuild only the two
unchanged research-HEAD targets in private objects, smallest target first.
Both source files already contain the repairs requested by the fallback route.
No source change is currently indicated for research.

## Consumer replay requirements

- `R1Z/EventsR1P2`: `R1Z/AgreeR1P`, `R1Z/AgreeR1P2`, `R1Z/EventsR1P3`, `R1Z/EventsR1P4`, `R1Z/FinalR1P`, `R1Z/PrivacyR1P`.
- `R1Z/SimCostOuterRetry6`: `R1Z/SimCostPass6Audit`.

All affected consumers should be recompiled when integrating the repaired
objects into a coherent closure, with research sources and standard-axiom
checks. The pinned research graph has **no import path** from either repaired
module to PrivacyR1HeadlineDeployedReal. Their legacy P-tree has been superseded
by the endpoint's Bin tree. This repair alone cannot discharge the headline's
RustRealRefinement or any deployment condition. No full release replay claimed.
`downstream.json` stores the whole import adjacency used for this conclusion.

## Launch routing

The shared run-joint.sh hardcodes shared sources, objects, sent ledger and
receipts. The user prohibits writing rebuild files, shared objects and other
jobs' directories. local-lean.txt rule 5 prohibits build/launcher infrastructure
repair. A path-only private copy is prepared in run-private.sh, with its exact
diff in launcher-path-only.diff. The task explicitly authorizes compilation in the assigned private directory;
this routing was used without changing shared infrastructure. No cap, lock or reservation logic changes are proposed.
The private receipt driver run_host.py uses the existing reservation helper
and the unchanged shared run2.py; it does not create a second build workspace.

## Repair receipts

Both targets: **environment repaired, source unchanged**. No research proof edit
is needed. The stale target source selections caused the old failures; no strict
dependency source correction was needed. Historical proof text and the existing
research replacements are recorded exactly in the `.diff` files, not introduced
by this job. The existing theorem statements remain identical.

| Attempt | Target | Exit | GNU wall | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| 35900 | R1Z/SimCostOuterRetry6 | 1 | 0:00.09 | 190884 | 0 |
| 35901 | R1Z/SimCostOuterRetry6 | 0 | 0:01.75 | 3598476 | 0 |
| 35902 | R1Z/EventsR1P2 | 0 | 0:02.13 | 3611184 | 0 |

All three sources are pinned at research revision
`3dbbe11f663278482e9382c451226c2c3fbc3ec8`. Successful source hashes are the
research hashes in AUDIT.md. Full source/dependency/object hashes, commands,
reservation receipts, wall/RSS/swap/caps and complete printed axioms are in
`receipts/receipt-35901.json` and `receipts/receipt-35902.json`; raw output,
time and admission logs are retained beside them. All 18 original axiom prints
are subsets of [propext, Classical.choice, Quot.sound]. Historical failures
30431 and 30485 and their time logs are retained, not rerun.

35900 failed before elaboration: Lean selected the private R1Z directory and
could not find its SimCostWriter object. Binding the existing hash-matching
R1Z dependencies and companions through private symlinks fixed the namespace;
`receipts/baseline-bindings.json` records all 16 bindings. This was an explicit
environment change, not an unchanged retry. No memory failure was retried.
Research EventsR1P2's already symbolic proof succeeds, so fallback bisection
or a new cardinality proof is neither required nor justified.

A separate PV_Env_Axioms module is prepared to audit every theorem, including
pubC_tame (omitted from the original module's print list). It adds no theorem.

Lean compile attempts: 3 / 60 so far. Kani: 0. No local Lean invoked.
No full manifest replay: this is a focused source-selection repair.
The two private objects are retained for the lead's integration; shared
sources, objects, env and launcher remain unchanged by this job.
