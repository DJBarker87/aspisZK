# Capacity-error relaunch reconciliation

Automatic relaunch 1 recovered branch `codex/pv-b3q-20261029` at
`2a1d585990`, with a clean worktree. The requested entry revision
`a9c78a0674` is the ancestor of the five completed continuation commits.
The existing FINAL.md and RESIDUALS.md already record the completed budget.

Read-only reconciliation counted the individual receipts independently:

- 80 distinct charged Lean attempts: 72 exit zero, eight exit one; **80/80 used**.
- 22 native scopes: 17 exit zero, four exit one, one exit 101; **22/30 used**.
- Zero Kani runs. No new host scope or Lean compiler was launched on relaunch.
- All 80 executed Lean snapshots match their receipt source SHA-256.
- All 102 receipts record MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0
  and zero swaps.
- Audits 77097/77098/77099 all exited zero at source revision
  `be4bd9576167b482a03b28679e56f90d41799d9d`; their recorded wall/RSS
  values agree with FINAL.md. The summary retains 148 theorem axiom entries.

The first local reconciliation script selected the wrong pathlib component
for scope names and failed its count assertion before performing checks.
The corrected read-only script used each receipt's enclosing scope directory
and completed all checks above. This was not a Lean/native scope or proof run.

The remaining eight native slots do not replenish the exhausted Lean budget.
No unvalidated proof is added, no unchanged full replay is repeated, and no
formatter diagnostic is un-quarantined. Per-entry standing remains in
catalogue-status.json and GROUP-STATUS.md. Complete fmt-1(a) source/event/caller
association and the actual-family closure14 instance remain OPEN; the existing
five-entry instance remains partial. No endpoint premise is removed, added,
weakened or moved into T. The privacy target is not established.

Next formal deliverable: resolve the 16 opaque concrete helper instances and
pre-inline/drop composition, connect named guards to actual endpoint events,
then instantiate the existing closure14 for the complete reached family under
a fresh explicitly assigned Lean budget. A formatter-consumer rebuild and
standard axioms audit are still required before lifting its quarantine.
