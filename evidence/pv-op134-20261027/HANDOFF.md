# V230 / op134 proof handoff

Branch: codex/pv-op134-20261027. Base: 848340629037f4f07a4454909880be8f587322c9.
Target not yet established. V230 remains OPEN. No shipped code or shared env-J
source changed; no Kani run; no wallet/key operation.

## Direct extraction

| Target | Exit | Wall | Peak RSS KiB | Swaps | Source revision | Axioms |
|---|---:|---:|---:|---:|---|---|
| charon-op134-001 | 0 | 38.45 s | 579200 | 0 | 8483406290 | N/A extraction |
| aeneas-op134-001 | 2 | 0.23 s | 52800 | 0 | 8483406290 | N/A extraction |

Exact commands, input snapshots and metrics: each target's receipt.json and
raw logs. PINNED-TOOLS.json pins the unchanged binaries. SOURCE-BODY.json
checks that the complete frozen shipped hiding file is the exact prefix of
the previous cbmid extraction context, followed by inactive harness cfgs.

Exact refusal:
`ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics`.

op134 was absent from the historical extraction inventory; this is a new
explicit op134 refusal. Historical cbmid 180/900-second masks comparisons are
retained as prior evidence and were not rerun. No extraction-source equation
is asserted. See ROUTE-II.md for the precise proposed owned index-loop shape,
prover caller redirects and preserved compiled-verifier path.

## Checked reference work

* PV_Op134_InventoryCallback.callback: complete outer Aeneas Result / inner
  Rust Result success; 3,803 cells; bounded coordinates; Nodup; all free;
  every free cell in the 1024 x 16 grid occurs. Coverage uses a finite
  cardinality argument, not reduction of the whole finite universe.
* PV_Op134_RowSpec.run/callback: complete Result row materialization, 214
  rows. The arbitrary-output run retains its explicit capacity hypothesis;
  the callback discharges it for the fresh empty vector.
* PV_Op134_RowOrder.sorted/nodup/dedup: ascending row order, uniqueness and
  dedup identity of the exact reference row list.
* PV_Op134_Masks.source: the full reference Result is exactly Ok of the
  64-entry U16 array. MaskBits0–7 cover all 1024 bit positions against row
  membership.

Also checked: global MaskSpec.bits and ReferenceBundle.cells_reference,
rows_reference, and op134_reference, universally over the selected base and
callback dictionary. Final audits both passed at committed proof revision
60da31b155fd7633e40b0cf944f84db2d2765907: 50297, exit 0, 2.62 s,
2669572 KiB, zero swaps; 50299, exit 0, 2.44 s, 2672788 KiB, zero swaps.
The complete new-theorem audit reports only subsets of
{propext, Classical.choice, Quot.sound}. 50298 was an uncharged reservation
refusal. The Lean budget is exhausted at 100/100 (93 successful runs and
seven retained failures), Kani 0/4. No unchecked current Lean module remains. Successful per-module receipts, not draft source presence,
are authoritative. AUDIT.json is regenerated after completed stages.

## Premise accounting and scope

Before: PV_CBM_CallbackBundle already supplied reference equations for
ops 132/133/134; inventory length/all-free and cardinality were separate.
After: the checked reference list has uniqueness/completeness and the exact
rows have order/dedup and bit membership facts. Every PV_CBM source and
statement is byte-stable; check.py verifies this against the base.

No premise of PrivacyR1HeadlineDeployedReal.privacy_headline_deployed has been
removed, added, weakened, or moved into T. V230's complete native source link
remains a P obligation. The capped trust list is unchanged. The source copy
and its deployment adoption are proposed only, not implementation work in
this branch. The three release ELF pins are unaffected by these proof-only
changes.

Focused objects reuse the restored private overlay. PARENT-OBJECTS.json
checks 85 reference object identities against latest successful parent
consumer receipts. This is not a from-source deployment-closure release
replay; see CACHE.md. Every compile receipt records target, source revision
and working-source hash, dependency fingerprints, exit, wall, RSS, swaps and
full axioms output. The final audits pin the committed proof revision above. RECEIPTS.tsv
indexes all 100 exact target/exit/wall/RSS/swap/revision/source-hash/axioms
receipts. FOCUSED-MANIFEST.json pins all 93 source hashes; AUDIT.json confirms
each matches a successful receipt. This is not a deployment-closure release
replay. New object hashes and sizes are in OUTPUT-OBJECTS.json; borrowed
dependency scratch, snapshots and Cargo targets were removed. Only the 93
new proof outputs remain as a small handoff cache; dependency rehydration
is required before another Lean invocation.

## Resource failure and next delivery

PROOF-REFINEMENT.md records the failed 214-push reductions, the -M7000 memory
failure, and the accepted symbolic replacement (50106, 13.53 s, 3019216 KiB,
zero swaps). No cap or recursion/heartbeat limit was raised. Failed receipts
are retained and excluded from accepted axioms evidence. Optional generic
indexing/transport drafts are uncompiled text under drafts/, not assumptions
of any claimed theorem.

Next native delivery: apply the owner-approved prover-only route (ii),
extract its owned helper with the pinned tools, and prove the complete Result
shipped/candidate association in Lean. Preserve the original shared statement
and static compiled-verifier schedules. No arithmetic Kani gate is pending.

Final ID tally: 127 distinct IDs consumed (100 charged, 27 uncharged),
including all three reserved audit IDs. Next unused assigned ID is 50124,
but this task has no remaining compile budget. TALLY.json preserves the
terminal sequential allocator cursor separately; no ID outside the assigned
range was used. All commits are local and path-limited; no push was made.
