# Ledger refresh 9 handoff

**303/599 CLOSED, 0 QUALIFIED, 296 OPEN. Target not yet established.**
Branch codex/cx-ledger9-20261105. No push, merge, shipped-source change,
new theorem, Kani, extraction or wallet/key operation.

## Exact claim and counts

NGZ_LEDGER.json.xz is the authoritative refreshed ledger, with uncompressed SHA.
NGB's 599-row basis and C0032 reproduce through the unchanged NGB apply producer
and LEAD_B007 compiler/source corroboration. C0032 adds the reviewed callback
edge to the existing TX1:310, without a new row or slice membership change.
All25 unchanged baseline/delta/support/Pool/plan validators reproduce in a private
write sandbox, with hash-checked sparse/compressed inputs. No predicate removed.
NGZ_VALIDATOR_PROVENANCE.json pins the validator sources; NGZ_TESTS.json rejects
15 evidence mutations. The22 new row promotions reproduce exactly.

| Scope | Total | CLOSED | QUALIFIED | OPEN |
|---|---:|---:|---:|---:|
| TX1 |353|164|0|189|
| TX2 |246|139|0|107|
| S |97|97|0|0|
| Q |161|147|0|14|
| D |345|63|0|282|

Four S/Q occurrences overlap and count once globally. S roots7/7 and Q2/2
remain CLOSED conditionally; D entry occurrences remain OPEN. Pool has no
consumer row in the verifier inventory; B/D remain OPEN. Routes:287 ordinary
(y),2 (y)/(ai),4 (ad),4 (ae),6 source reclassifications. Pool A is (af) outside
the599 rows. No (ah) credit: TX1:036/040/041/043/044 remain OPEN TOOL-BOUNDARY.

## Second all-slices composition test

NGZ_L003 imports NGK canonical Pool plus every new selected S/Q/D/support
forest, NGP/NGR/NGS plan results and AspisR1.RPx_Deployed.deployed in ONE
environment. NGZ_AUDIT.json raw-walks5,663 unique selected roots, including
all historical manifest roots, auxiliaries and every explicit forest-import
root: standard axioms only, zero collectAxioms disagreements. All8 planted/
mutation fixtures pass in the SAME compiled proof binary. Walker bytes equal
NEP_WALKER, and its compiled object matches NGK's conformance pin. Full driver
diffs and root completeness/provenance are committed.

NGZ_SCAN.json:13,761 modules,694,257 declarations,24,647,896 references;
ZERO dangling references, incompatible owners and import mismatches. The1,666
compatible cached replicas are disclosed. NGZ_CONFLICTS.json records NONE;
no row is qualified by a forest conflict. NGK's canonical retarget resolves
the historical ledger8 Pool conflict; no forest was patched or renamed.

Retained excluded attempts: L001/L002 missing cached dependencies; L033: 327
false import-baseline failures caused by our parser omitting implicit Init.
NGZ_BASELINE_REPAIR.json derives corrected lists from committed non-prelude
sources, and L034 passes with the SAME scanner binary. No failed import or
scan is promoted. NGZ_PREFLIGHT_FIXES.json records all own-input repairs.

## Honest security and plan statement

NGZ_STATEMENT.md and NGZ_STATEMENTS.md quote26 full existing kernel statements
and exact axiom output from L035–L040. Three of ten adopted plan items are
proved conditionally: HISTORY.saved_to_loaded
(AspisR1.NGR_HISTORY.saved_to_loaded), CARRIERS.same_inputs_or_collision
(AspisR1.NGS_CARRIERS.same_inputs_or_collision), and ORACLE.partial_and_returning
(implemented by AspisR1.NGP_OracleTransport.prefix_of_native/exact_of_returns).
All four exact exported names print [propext, Classical.choice, Quot.sound].
These do not provide their native-observation hypotheses. No theorem named
partial_and_returning was fabricated.

NGZ_SHORTEST_PATHS.md recomputes the current necessary entry-to-accept call
paths; both OPEN sequences match NGJ. NGZ_REMAINING.md preserves NGG items1–10
and distinguishes resolved canonical coherence from still-unretargeted NGG
production-prefix support. B/D production same-execution admission/settlement,
D producers/drivers, actual ordered transcript, L159 physical_instance and
L181 experiment association remain OPEN. Ruling(aj)'s L159 physical reporting
boundary and any uncovered adaptive reorder are owner decisions; recommended
Pool B/D completion and the current partial terminal policy continue unchanged.
L187 cold coherent replay and L188 final trust/axiom/source/artifact audit remain.

## Assumptions, freeze and resources

Nothing is discharged or silently removed from accepted trust. Retained:
P6/D188 option-A native contract semantic transport (RECLASSIFICATION), SDK/
std/allocator/ABI/compiler/Aeneas/source-to-ELF realization, RuntimePersistence,
digest/H and cryptographic assumptions. RuntimeReturnData nonempty1..1024
(ASR8=792) and RuntimeMemcmp are ACCEPTED. RuntimeClockSlotBinding is
ADDED-LEAD (same instruction bankSlot only), inventoried with open plan use,
no new CLOSED row. RuntimeCpiReadonlyEntry7 is ADDED-PENDING-LEAD, UNUSED.
NGZ_TRUST_USED.json separates direct certificate use from retained realization.
L154 is a statement parameter; coherent digest/error slots are op43/op44.
Privacy, two transactions and100-bit PER-ATTEMPT target are unchanged.

Crates/programs are byte-identical to frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
No ELF rebuild trigger. INHERITED ONLY, not rebuilt/rehashed here: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

40/40 slots used:11 Lean,27 audit,2 optimized links;37 successes,3 retained
input/baseline failures. Wall sum503.231128s; peak RSS7,070,900KiB; swaps0.
Every admission exit0 AND allowed:true; one own capped scope at a time,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean -M7000, links -O3.
No timeout, memory kill, cap increase or unchanged timeout retry. Exact targets,
commands, source revisions/hashes, direct/Aeneas pins, exit/wall/RSS/swap and
axiom lines are in NGZ_ATTEMPTS.jsonl and40 linked receipts.

## Cache, restoration and next deliverable

Initial NGK/new-export seed:30,415 paths,7,685,501,104 logical bytes,
7,665,173,608 unique bytes; supplements are separately hash-pinned. Owned cache
/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104 is retained.
NGZ_flat canonical copies were deduplicated ONLY against identical objects
inside that owned cache, atomically preserving all paths and hashes:29,974
replacements; total cache allocation16,632,720→9,179,836KiB. No predecessor
read-only cache or other worktree was modified. NGZ_EXPORT.json retains15
exports; NGZ_CLOSURE_PINS.json.xz pins30,354 actually resolved objects/sidecars,
including Aeneas. Restore NGZ_flat/NGZ_exports_20261105 FIRST, then NGZ_flat,
then coherent SInt2 workspace/objects and the pinned toolchain. Never restore
legacy Pool precedence.

NGZ_PACK.json stores60 repeated large source inputs once by SHA with resolvable
references. NGZ_HOST_END.json records only hash-verified removal of exported
NGZ workspace outputs and locally archived raw graphs; cache, sources, receipts
and keys remain. No file over20MB or Python bytecode/object/binary/ELF/tarball
is committed. This is a focused cached hybrid checkpoint, not a cold release
replay or deployed security theorem. Next deliverable: close actual D/native
producer and Pool B/D associations under the adopted plan, then L187/L188.
**Target not yet established.**

Stage commits:3a21a58b9f8 scope;72d714cdf29 reproduced ledger; subsequent audit
and final packaging stages are recorded in this branch's Git log. No push.

Final artifact verification: NGZ_ARTIFACTS.json PASS,5,715 archive/SHA checks,60 packed input references,152 receipt source hashes,all13 requested outputs and26 full statement quotations. Host cleanup verified5,686 own rebuildable paths (882,691,661 bytes); retained exports/cache and no active own prover. No file exceeds20MB. Authored Python/Lean/Markdown whitespace checks pass.
