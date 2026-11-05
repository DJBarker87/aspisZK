# Ledger refresh 9 handoff

Work in progress. Branch codex/cx-ledger9-20261105. Target not yet established.

Scope: reproduce the 599-row NGB basis and reviewed C0032 producer overlay;
validate post-NGJ deltas; compose NGK canonical Pool/verifier forests, new slice
forests and the NGP/NGR/NGS plan results with RPx_Deployed.deployed. No new
theorem, Kani, extraction, shipped-source edit, push or other-worktree mutation.

Budget: 40 Lean/audit slots, zero Kani/extraction. One admitted capped scope at
a time, 6G high / 8G max / swap0 / 64 tasks, Lean -M7000. Admission requires
exit0 and allowed:true. Record exact targets/revision/hash/dependencies,
exit/wall/RSS/swap and full axioms. No unchanged timeout retry or cap increase.

Initial authority: NGJ 281 CLOSED / 0 QUALIFIED / 318 OPEN; NGK canonical Pool
composition 4,714 roots, standard axioms and zero scan defects. These are
inherited evidence pending this refresh, not newly reproduced claims. Expected
post-delta count 303 CLOSED is a hypothesis to check. Pool B/D, source/runtime
realization and L187/L188 remain open. Final receipts and findings will replace
this provisional handoff incrementally.

## Ledger stage

Reproduced 303/599 CLOSED, 0 QUALIFIED, 296 OPEN: TX1 164/353,
TX2 139/246; S 97/97, Q 147/161, D 63/345 (four S/Q overlaps).
All sixteen post-NGJ delta/support/Pool/plan validators pass, unchanged predicates.
C0032 reproduces through the unchanged NGB producer and LEAD_B007; no count
or membership change. Five field-helper rows remain OPEN TOOL-BOUNDARY.
The exact shortest OPEN paths match NGJ. The new combined import L003 passes
with RPx and the proved plan results, standard axioms only. Full raw audit,
fixtures and scan remain in progress; no completed audit is claimed yet.
