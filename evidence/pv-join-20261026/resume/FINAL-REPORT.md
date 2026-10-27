# Resume result

Branch `codex/pv-join-20261026`, base `c9d2b33137`. **Budget exhausted: 100/100
host Lean attempts; 89 accepted, 11 failed. No Kani or local Lean compiles.**
The privacy target is not established. No endpoint premise was removed,
weakened or added, and no checked shipped-source ROW counterexample was found.

Checked results, each with exact source/dependency fingerprints and axiom reports:

| Target suffix (R1Z.PV_Join_) | Receipt |
|---|---|
| ParserTransport / NegTransport | 35333 / 35345 |
| Current71 / Current100 / Current101 | 35369 / 35375 / 35372 |
| EmbeddingWord / Embedding (op110) | 35377 / 35380 |
| CB3Flat / CB3Boundary (op51/120) | 35352 / 35379 |
| HeapCompatibility (concrete op32/op12) | 35383 |
| StoreLedgerSource.body_source | 35384 |
| NativeOp20Carrier.carrier | 35400 |
| NativeAudit.data_of_model_bytes | 35349 |
| PublicInstall | 35404 |

The ledger theorem instantiates the explicit RunJoin `BodySourceLaw` with
`ProverRwP6BodyStore.selected`, retaining native RNG/erasure instances. It does
not associate that interpreter with native filesystem/oracle effects or actual
fixtures. The op20 theorem specializes the concrete bijection to
`PV_CB_Op229Transport.native` and CB3's installed carrier; it does not equate
whole dictionaries. PublicOp20.selected_source, PublicCaller AuditProjection,
and PublicCaller LedgerSource remain uncompiled drafts.

**Inventory 30 → 30:** 4, 32, 33, 34, 35, 36, 79, 117, 121, 122, 123, 132,
133, 134, 222, 223, 224, 226, 227, 228, 230, 232, 249, 250, 251, 252, 253,
257, 258, 259 remain without a joined source law in this caller. Correspondence
for already-selected entries does not decrement this inventory.

For **both transfer and withdrawal**, neither independent proof-byte equation,
complete audit/status observation equation, whole V163 data equation nor native
release non-vacuity is proved. NativeAudit proves canonical successful audit
values universally, including the emitted attempt prefix. Its whole-data theorem
still assumes the independent model-byte equation; actual bytes never define
the mathematical model. Actual public/compiled fixture and world associations
remain open.

**Final audit: non-green.** Corrected FinalAudit explicitly imports the headline.
First required attempt 35304 failed on its missing object. The original headline
then checked at 35323 with standard axioms. The local budget guard prevented
35405 before launch: one slot was miscounted when planning the final retry.
Compile-free final preflight lists 79 missing project objects; no final manifest
replay or successful combined closure audit is claimed.

All accepted reports use only propext/Classical.choice/Quot.sound. Peak RSS:
4,457,092 KiB; swap: zero. Every target's exit, wall time, RSS, swap, revision and
axiom output is in `receipt-index.json` and individual receipts. Restored cache
provenance and 13 coherent reused objects are recorded; differing overlaps were
not overwritten. No shipped code, keys, sibling worktree or launcher changed.

Next: finish missing audit dependencies and combined audit, then prove the
independent byte-result equations for the actual compiled fixtures, native
world/effect association, and both native non-vacuity witnesses. Commit history
since the base is recorded in `commits.txt`; the final evidence commit follows it.
