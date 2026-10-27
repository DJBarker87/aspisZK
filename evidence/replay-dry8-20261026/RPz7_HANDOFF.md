# L187 Phase transport and coherent replay handoff

**S2/L187/L188 OPEN; target not yet established.** Branch
`codex/cx-replay-dry8-20261026`. Local stage commits only; no push or merge.
Only RPz7-prefixed sources/evidence in this job's directory are changed.

## Established repair

RPz7_PhaseIso explicitly maps all11 producer verifier.Phase constructors to
FirstCaller.Phase and back, retaining every U8/Usize payload. Both round trips,
an Equiv, arbitrary callbacks, optional observers (including None), and
observer-consuming functions are checked. Generic laws use no axioms or
Quot.sound. No nominal equality between the two inductive Types is asserted.
The existing FirstHelperBinding.phaseToFirst supplies the constructor pattern.

RPz7_PhaseConsumers checks mark,verify,finish and both code consumers, plus the
definitional retained-carrier equality and .Parsed non-vacuity witness. All7
new theorem axiom lists are empty or subsets of propext,Classical.choice,
Quot.sound (1479/stdout.log). The carrier equality concerns the new abbreviation
and FirstCaller.Phase,NOT the producer inductive. Exact transport sources,
axioms,commands,revision/source/dependency hashes and resources are committed.

Original S1SemanticPhaseV1 has ZERO theorems; its sole declaration is the
conflicting abbreviation. RPz7_STAGE1.md gives the complete export comparison
and empty per-theorem restatement table. Replacement removes that declaration.
All27 legacy carrier sites in21 modules route through RPz7_PhaseIso.Phase,
definitionally FirstCaller.Phase.18 of21 modules compile; RawJ_VerifyRead,
RawK_VerifyHead and F3U_VerifyHead remain unbuilt. No original/session A file
is changed. All1835 copied consumers differ only by imports and the recorded
carrier substitutions (RPz7_source-adaptation-check.json);no proof body weakens.

## Checked composition and provenance

Accepted-pair Claims composition freshly passes at312; the lower deployed
Rc2_Top passes at1402 with exactly [propext,Classical.choice,Quot.sound]. These
are explicitly lower-root/model results,not the requested Rc7..Rc10 completion.
The larger producer is the historical e5c186ba3 Tx1 extraction against which
the Tx1 bridge was proved. Neither producer has been shown to be a complete
extraction of frozen D188; that provenance item remains OPEN. RPz6 provenance
and the23 source resolutions/Aeneas toolchain base are inherited by exact hash.
No historical proof is silently reassigned to frozen D188 or the release ELF.

## Actual top, statement gate, ledger and non-vacuity

Target: AspisR1.Rc10_Top.deployed. Complete BEFORE/AFTER SOURCE statements are
byte-identical:SHA256 fc89d7515e949c643df40078ebfd4322035ab120990aae686a8f0f621a34d8ff.
No fresh Rc7/Rc8/Rc9/Rc10 compiles. The required complete KERNEL byte-identity
comparison is **NOT ESTABLISHED**. Historical query1480 also fails before
reading its statement:the pinned top object matches4a8fd228…/218680 bytes,
but its recorded path lacks
`codex-cx-import-union-20261022/objects/AspisR1CircleSampleWrapper/Funs.olean`.
See RPz7_SIGNATURE-BLOCKER.md for the exact full error/resources. That chain
stops without alternate source/object/root or unchanged retry. No statement
leakage is asserted or disproved;the semantic-leak gate was not reached.

Premises removed/added/changed **0/0/0**. Ledger method:actual plus deployment,
deduplicate L185=L159 and existing aliases,preserve classifications. Delta
**T0/P0/G0/C0**. Historical actual83T/12P/13G/0C and combined89T/16P/13G/0C
are unchanged;no fresh absolute kernel recount. No game,metric,failure event,conclusion or runtime trust item is changed.
The top's full quantifier/carrier/kernel identity remains a verification obligation.

The new transport laws have an actual .Parsed witness with no axioms. This is
not joint deployment non-vacuity. Historical conditional witnesses retain their
scope;no fresh simultaneous inhabitant of all Rc10 premises is supplied. No
false antecedent,hidden conclusion or new source-refinement assumption is added.

## Completed budget, frontier and audits

**1498/1498 Lean attempts;0 Kani.**1497 pass;the sole failure is historical
inspection1480. All1478 source-stage attempts,the concrete transport module,
and all18 audit batches pass. No further Lean run is authorized by this round.
No compiler timeout,memory kill,cap increase or unchanged failed-input retry.

Original union closure4964 modules: **4605 green,0 failed,359 unbuilt**;
**62 ready,297 dependency-blocked,0 unresolved**. Reuse3128;new original
contexts1477. PhaseIso and PhaseConsumers are two additional checked contexts,
not extra original closure credit. Rc7:320 unbuilt;Rc8:341;Rc9:354;Rc10:358.
Rc10 excludes the extra requested Rc7_Top module,hence union359. Exact lists,
selected/prefixed names and per-root counts are RPz7_frontier.json.

18 batches audit1510 contexts (including31 inherited larger-producer contexts)
with **19467 structured queries and19467 full raw #print axioms results**.
3097 unchanged contexts reuse hash-checked historical audits;combined queries
116306. All1510 effective ordered import headers match. Raw metadata repeats
Init;three source headers also repeat an explicit import. Deduplicating only
identical names,preserving first order,matches the source plan;raw logs remain.
The local result-extraction correction ran no Lean (import-normalization.json).
123 global names recur across contexts;no proof-term identity is inferred.

All180 historical formatter records are present,with unchanged axiom sets and
exactly the same85 nonstandard axioms. No nonformatter declaration depends on
those axioms. Thus the all-declaration standard-only gate is FALSE solely for
the retained formatter families;the new Phase laws are standard-only. The
requested fresh-Rc10 proof-term reachability is **UNKNOWN for each of180
records**,explicitly null in RPz7_formatter-records.json. Partial-context or
lower-root audits are not substituted for that missing yes/no result.

## Resource and hash receipts

Each compiler uses the unchanged S2W runner,one admitted scope at a time,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64,Lean-j1-M7000-async=false.
Each receipt has exact target,argv,source revision/hash,dependency hashes,exit,
wall,peakRSS,swaps,cgroup and full printed axioms/errors. Aggregate compiler
wall **4325.6183725127485s**,peak **6677248KiB**,swaps **0**;
wall excludes SSH/admission/git/collection time. There were0 reservation retries.
The local dispatcher was interrupted between completed003/004 to cache an
already-read plan;no Lean process or unchanged compile was restarted.

Final verification:all1498 compiler snapshots,4964 original planning inputs,
3128 actually selected reused sources,and6648 input/output artifact paths
hash-match.22637 trusted-base paths checked;the sole known nonlibrary drift
is unchanged S2H_reservation.py f5b8318a…→195657d7…(inherited,not edited here).
No Lean/library/tool runner drift or other hash error. Default Lake object
directory absent. Exact evidence is RPz7_final-verification.json and host-validation.
After verification,18 query-only compiled artifacts/links were removed;accepted
source proofs remain pinned as the continuation cache. No live RPz7 compiler
or runner remains. No binaries are committed.

## Artifacts and next deliverable

No shipped Rust,cfg(kani),SBF,key,ELF,other worker's worktree/candidate or
source adoption changes. No ELF rebuild trigger. Historical pins only:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Continue the62 ready vertices using the pinned RPz7 view/objects under
`/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`;do not rebuild
valid unchanged modules. Complete359 original vertices,then the requested
fresh tops,full kernel comparison,top axioms and180-record proof reachability.
Resolve D188/source-to-ELF provenance and joint non-vacuity separately. The
100-bit release target remains unestablished.
