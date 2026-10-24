# Current status: 100-bit soundness and privacy (living page)

## Current coordinator checkpoint — 2026-10-24 10:55

Both deployed security targets are **not yet established**. This checkpoint
supersedes the older progress descriptions below; their theorem statements
remain historical evidence.

Soundness: the owned adapter is proved to its named runtime/child boundary
(`S2W_D189Consolidation.accepted_run`). The merged Q1 packet proves actual
query/flush state correspondence to frozen2 conditionally; Q2 derives same-TX1
checkpoint provenance and current reader-helper transports. Remaining lead
work includes indexed authentication, native op18 and saved-to-resumed state,
then enclosing oracle/runtime/artifact composition. Session A owns concrete
prepare/op7, powers/op17, S3/S4/S5/S9 backends, S6 and S10 lowering.

Privacy: current real-side endpoint is
`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`, against mathematical
simE (D185); native simulator refinement is not required. The prover rewrite
and CT v2 candidates remain unmerged. D190 records a proved obstruction to a
pure randomness dictionary and authorizes an effect-aware proof repair.
Real-run refinement, joint L1/L2 coupling, the client proof-account route,
quiet-host under-15-second timing and final adoption/release audits remain open.


Last updated 2026-10-22 02:05 by the lead. This page is the single current
reference; dated notes keep the history.

## The contract

`design/SECURITY-CONTRACT-20261021.md`: **100-bit per-attempt soundness
without grinding credit.** (A) One attempt fails with probability ≤ 2^-100;
in particular the whole-experiment bound for an adversary making no queries
is ≤ 2^-100. (B) Repeated attempts are stated plainly as (starts)·B +
collision terms, keeping the Q-dependence. Everything below is in the
random-oracle model (SHA-256 as an ideal hash, premise P1).

## Soundness

**Headline: `OraclePortHeadlineFrozen2PerAttempt.final_soundness`**
(`lean/OraclePortHeadlineFrozen2PerAttempt.lean`).

    F ≤ (Q+34)·B + κ(Q+1161) + 2^-126 + 2^-454,   B = 15/2^109 ≈ 2^-105.09
    zero_queries:  F ≤ 2^-100

Here F is the failure probability of the deployed two-transaction flow
(stage 1, checkpoint, Pool stage 2), modelled exactly by `dV_frozen2` with
the frozen multiproof order and the six checkpoint reads. Q counts every oracle
query the adversary makes. The extractor cost is ≤ 4·scale³·(Q+2323)³.

| Premise | Meaning | Status | Owner |
|---|---|---|---|
| `hqueries` | the adversary makes at most Q queries | experiment parameter | — |
| `AcceptedRunJoin D rust` | on every accepted run, the frozen Rust's oracle log and outputs equal dV_frozen2's | open: split into per-cone joins (table below) | see below |
| `StoredCarrierBinding` | the runtime presents the same stored proof and accepted observation across both transactions | reduces to the same execution join plus the named runtime premises P2/P2′/P3/P4 (`STORED-CARRIER-20261021.md`) | lead |

Contract status: (A) and (B) are met **conditionally** on these premises.

Per-cone joins (`JOIN-SPLIT-DRAFT-20261021.md`, `CONE-AUDIT-20261021.md`):

| Cone | Status | Owner |
|---|---|---|
| S1, S3, S4, S5, S6, S9 | in progress (session A keeps S1 and S6; S3/S4/S5/S9 as before) | user's Codex |
| S2 (top-level verifier and adapter caller) | ownership transferred to the lead on 2026-10-23 (handoff `S2-OWNERSHIP-HANDOFF-20261023.md`, branch `codex/s126-caller-20261021` tip `0182d4eb4f`); diagnosis and plan job running | lead. **Critical path** |
| S7 | reference = dV_frozen2 stage, total; frozen caller adoption waits on S2 | lead (paused) |
| S8 | reference = dV_frozen2 stage, total, composed with S7; caller adoption waits on S2 | lead (paused) |
| Checkpoint ABI | success-conditioned stage join with the six ordered digest reads proved to dV_frozen2 at the decision position (`CheckpointBytes5Decision.decision_success_join`, 2026-10-22); remaining premises exactly `S2S10CallerBinding` and `S1S7S8StateProvenance` | lead (waits on S2, S1/S7/S8) |
| Parser and multiproof | parser complete against frozen rows; multiproof stage join `both_batches` proved (c), conditional on caller binding and Rust carrier P6 | lead |
| S10 inventory | every declaration assigned; 140 CFG ordering facts kernel-checked; gates exit 2 pending the caller identities | lead (paused) |

## Privacy

**Headline: `privacy_headline_admitted`** (`v8-r0-zk-20261009/lean/R1Z/`, LOG D122).

    ε ≤ 2^-109 + 2^-137 + 2^-454 + 128(M+1)/2^190 < 2^-100,   M ≤ 2^25

Discharged at the protocol instance: causality, the commitment families,
read coverage, history laws, all accounting rows, the wire batch and log
premises, `CallerLaw` (D120), and builder soundness on the admitted input
domain (D122). The simulator cost is relative to the adversary's input:
replay ≤ c·(n+1), cache ≤ C·(n+1)².

**Caveat (D124, 14:30):** at the fixed-observer specialisation the two execution
joins became identities and were deleted, so the headline is a **model-level**
theorem. The deployed claim needs the explicit premise `RustProverRefinement`
below. D111's wire discharge must also be redone over the *ordered* q22 queries,
because the shipped prover batches by order, not by set.

| Remaining premise | Meaning | Owner |
|---|---|---|
| `R_wire_builder_checker_D75_retry` | the shipped prover's whole run (builder, checker, retry) equals the model run outside the named bad event | lead: prover part 15 (observer fixed, QM31 transport, retry history) |
| `G_sim_R_wire` | the source simulator's ideal run equals the model's | lead, after the real-run join |
| `sim_preparation` | concrete preparation cost for simulator efficiency | lead (paused; needs a new env-J range) |
| `RustProverRefinement` (explicit since D125, `PrivacyR1HeadlineDeployed`) | the real shipped prover's whole run (builder, checker, retry, ordered serialisation, observer) equals the constructed source outside the bad event | lead: prover part 16 |
| Ordered-q22 wire encoding | done (D125): ordered 10+12 batches, bound unchanged | — |

**Scope (user, 2026-10-22, LOG D159):** timing and other side channels are inside
the privacy contract. Leakage levels L1 (attempt/retry/error counts), L2
(source-level branch/index/trip-count trace) and L3 (compiled code and
hardware; trust item or measurement only). A side-channel inventory of the
deployed prover is the first step.

## Release gates still to run

1. The cross-cone instance-naming fix (`IMPORT-UNION-20261021.md`), so that
   all cones import together.
2. One canonical frozen-manifest replay, once all cone joins are green
   (AGENTS.md cadence).
3. The `#print axioms` audit on the final headlines.


### Lead checkpoint — 2026-10-24, Port6AUTH reviewed

Port6AUTH_Query.accepted and the sufficient unchanged-bound source headline are
merged at915db3ef07. Full-driver CleanAcceptedModel, trace/count/runtime
instances remain open; no all-H join or deployed closure claimed. Port7CLEAN
is assigned concrete terminal Checks/no-hit composition. Port6CK remains on
native checkpoint resume. Prover RNG preflight runs on H5-aligned candidate
71100fccbd under D191; still unadopted. Both targets not yet established.


### Lead checkpoint — Port6CK reviewed, 2026-10-24

Actual saved-to-resumed equality and current reader ordered observations are
proved under explicit local preparation/primitive/runtime interpretations.
Port6CK_Complete.accepted consumes the actual returned state; the earlier
literal same-state premise is removed. SourceJoin.source/provenance are ready
for VTop reader_join/writer_join and Port7CLEAN composition. Authentication
and source-driver obligations remain explicit. Both targets not yet established.


### Lead checkpoint — source-call terminal Checks, 2026-10-24

Port7CLEAN is reviewed/merged at a23a58fb09. Terminal Checks follow from the
explicit local source-call premises; full CleanAcceptedModel/no-hit does not.
A value-only driver counterexample identifies the missing concrete effectful
body instance. Port8EFF owns actual batch/checkpoint effect installation and
reached-call embeddings; Session A op7 must supply ordered sampler effects.
The current worktree includes reviewed Port6CK for saved/resumed integration.
Source1161, runtime binding and release replay remain open; targets not established.


### Lead checkpoint — conditional checkpoint effects, 2026-10-24

Port8EFF installs actual checkpoint Code and proves conditional ordered effects,
first-source reader provenance and all-outcome reader count<=3. Its Program
currently ignores oracle replies after recording them and retains fixed-native
Oracle agreement. It is NOT yet a fixed adaptive source probability experiment.
Port9OR must repair/justify reply-driven interpretation before op5 expansion.
Batch/sampler/no-hit/source1161/runtime/artifact obligations remain open.
Both targets not yet established; no conditional merge is deployed closure.


## Port9OR review: reply-driven physical source effects (2026-10-24)

Reviewed worker e45800d44e and merged its four commits. Port9OR_Code.correspondence now equates a fixed reply-driven Program with pointwise native interpretation, preserving full returns and ordered successful-read prefixes on all outcomes. Reply byte/state round trips are proved. Reader/batch lazy laws quantify arbitrary rational observations under that one fixed law. Existing primitive success/fail/div policy and source/lowering boundaries remain; this is not real SHA equality with every H or a new artifact identity.

Port9OR_Installed.effects installs physical op5 alongside8/18. FirstBatch.first_batch derives the reached batch1 observation inside the same first accepted source record, with actual saved checkpoint/current18 p/a and p.gamma powers operand. P6/source lowering, primitive instances, canonical parsed binding and Session A prepare7/powers17 remain explicit. Rejection.no_sampler demonstrates why unconditional charged-sampler containment is unavailable at actual decoder-rejection paths (local decoder premise, not a deployed fixture). Accepted-source failure domination/no-hit, source1161, StoredCarrierBinding and release linkage remain open. Exact bound (Q+34)*B+kappa(Q+1161)+2^-126+2^-454 is unchanged. Both deployed targets remain not yet established.

Lead read complete Code/Reply/Law/Installed/FirstBatch/Batch/P6Verify/loop/rejection statements and stage boundaries. Independently reran receipt/cap/aggregate/axiom checks and inverse-lift audit read-only; both generators --check pass. All25 final source hashes match green receipts. Audit060: c4c08b5c81c6169cb08505f0cf0084591482b82d,exit0,1.917377429s,RSS4459028KiB,swap0,69 standard reports. Compilation reused; no full manifest or new ELF gate.60 new Lean attempts plus inherited36 =96/100,4 remaining;0/20 Kani.

Next independent producer is canonical sourceBatch read containment from the ACTUAL physical batch observation, consumed by Port6AUTH_Native.authenticated/Query.accepted. Their contains premise still refers to abstract sourceBatch rather than Port9OR physical logs. Prove that local accepted comparison and both reached batch embeddings without assuming the desired log containment. Prepare sampler/probability transport remains separately owned/open.


## Addendum (lead, 2026-10-24): physical-to-canonical authentication trace reviewed

Port10AUTH d1069e1971 is reviewed and merged. Installed.accepted equates the complete actual accepted physical op5 observation with canonical sourceBatch evaluation for either batch, deriving concrete PackedKeys from query binding. Source hash totality is not assumed: Port9 pointwise interpretation proves successful-call agreement; proof-only totalization is outside the sampled program. Duplicate hashes, count/padding checks, scratch and chronology remain intact. FirstBoth.accepted places both canonical batch read-containment clauses inside the SAME first accepted source record, retaining actual TX1 saved checkpoint/current18 pair and both physical witnesses.

Local upstream wire/length/parser/model query/root/node-view provenance and existing ParentGate/LeafGate/P6 lowering remain explicit, not discharged by universal implications. Before: Port4B batch theorem gave only existential canonical log success. After: exact physical/canonical observation and actual driver embedding, with named local provenance. No containment/no-hit/full-driver equality premise hides the result. Next: instantiate those provenance equations on the actual two witnesses and feed the resulting clauses into Port6AUTH; prepare7/powers17/sampler primitive frontier remains Session A. Failure domination/no-hit, source1161, StoredCarrierBinding and release linkage remain open. Exact probability expression unchanged; both deployed targets not yet established.

Independent read-only static review passed all23 final sources, direct source/dependency hashes, five generator checks, all caps/aggregate reservations and all41 standard reports (40 distinct theorems). Receipt064: c5dc5c0583 plus exact dirty-source hashes,exit0,2.422900571s,RSS4491516KiB,swap0. Compilation evidence reused; no full manifest or ELF gate. Resource failures040/053 were replaced by symbolic log composition and corrected anchored source cut; no cap increase/unchanged retry. Pre-Lean rejection033 counted.64 new attempts exhaust cumulative160/160;0/20 Kani.


## Addendum (lead, 2026-10-24): actual checkpoint provenance and indexed recovery

Reviewed Port11PROV2ab0c21054 and integrated its two commits. CheckpointQueries.accepted and CheckpointRoots.accepted prove exact raw query-array/two-root retention from actual TX1 Prepared through installed writer8 and current18 on SAME saved Vec, without canonical BodyMatches. Views derives fixed node slices and folded-root equality; FirstBoth reuses them for both actual batch witnesses. Authenticated.accepted derives indexed recovery in SAME first accepted source record via Port6AUTH_Recovery. Discharged supplied node views/folded roots and independent resumed query/root provenance. Retained initial parse validity, actual op7 query/root association, Std/unwrap/P6 gates, first-log cap/no-hit and root-frame facts. Query/terminal closure remains uninstantiated; no hidden conclusion was discharged by the universal local implications.

Independent static verification passed13final modules,29public theorem reports plus private helper,25attempt receipts/source hashes/resource/scope/generator checks. Audit025:4f4f0fd5cf3c54ed73cc9db36ec757366cea5479 plus exact hashes,exit0,2.2349480139964726s,RSS4476128KiB,swap0,standard axioms only. Compilations reused; no coherent manifest or ELF identity gate. New25/60used,cumulative185/220,35remain;Kani0/20. Concrete all-outcome leaf/node/row/writer component counts are proved, but SOURCE1161 remains open.

Next independent deliverable: physical row/level read-potential proof including supplied-node cursor and unresolved frontier, then actual batch counts. Source-audit arithmetic1040batch+6checkpoint+115transcript=1161 remains a calculation TO PROVE, not an accepted cap. Unrestricted rest still delegates actual op3/op4/op7/other bodies; full-source budget and provenance require their concrete owner implementations. Both deployed targets remain not yet established; exact probability bound unchanged.


## Resource-accounting correction (lead, 2026-10-24)

Read-only inspection of Port9OR_compile/Port10AUTH_compile/Port11PROV_compile confirms their admission scan is rooted in user-1000's user@1000.service and checks direct cgroup.procs in *.scope. It omits system.slice Docker/services and hierarchical populated descendants. Earlier lead statements that their static aggregate checks passed mean only the recorded SUBSET arithmetic; claims of complete historical aggregate<55GiB are superseded as unverified. Individual no-swap/MemoryHigh/MemoryMax/TasksMax and source/axiom evidence are unaffected. A new current host-wide finite capped subtree inventory found24.375GiB; this cannot reconstruct historical totals. Future admissions must include all populated capped subtrees once and retain unreadable/uncapped-background handling. Existing proofs are local mathematical evidence, not retroactively compliant resource/release certificates. D199 has the privacy finding and correction path.


## Addendum (lead, 2026-10-24): concrete owned physical count1046

Reviewed Port12COUNT9e393a861e and merged its three commits. Potential.node_funded/Rows/Levels prove physical read credit from supplied-node cursor plus unresolved frontier, including arbitrary digest failure/divergence and rejected prefixes. Verify.count derives domain from actual guards. Installed.batch0<=477,batch1<=563 hold for all inputs/H, with six concrete capacities discharged. Installed.owned_calls and checkpointChain_count give<=1046 for the four actual owned batch/checkpoint calls/projection. FirstReads explicitly derives first-read caps from total log length; repeated calls were retained. The projection is NOT the full driver. Full1161 requires actual delegated rest<=115 and control-flow composition, still open with parser/prepare/source sampler instances. Both deployed targets remain not yet established. Exact bound unchanged.

Lead inspected complete potential/verify/installed/projection statements and stage reports; independent read-only source/receipt/generator/axiom checks passed12 final green source hashes,36standard reports and per-job caps/zero swap. Audit029 atcd118a6bc6 with exact hashes:exit0,1.96390285299276s,RSS4414056KiB,swap0. Cached dependencies reused; no coherent manifest/ELF gate. Complete historical aggregate claim remains UNVERIFIED under the scanner correction recorded above; recorded subset arithmetic is not complete accounting. This limitation applies to this inherited launcher too.

Budget correction:28actual Lean launches plus1pre-Lean rejection reserved29slots. Preserve conservative charge of that rejection under manager policy:185prior+29=214/220 charged,6remaining (213actual compile count is separately valid). No slot reclaimed/reset. Kani0/20unchanged. Next independent premise-removal attempt can use only6 slots, and must implement complete all-scope resource admission before any heavy launch.


## Addendum (lead, 2026-10-24): indexed authentication without native totality

Reviewed Port13GATE c0796e88f5 and merged as 8f19bb29d5. Port13GATE_Authenticated.accepted preserves the complete Port11 sourceAccepted premise and subsequent witnesses/conclusion; native-D full P6Boundary and redundant binary callback are removed. A proof-only Unit dictionary constructs canonical comparison totality without replacing the fixed response-driven source Program. Actual native successes and original ordered logs still pass through Port10AUTH_Installed. Occupied/sibling ParentGate and LeafGate, strict parse/query/root association, Std/unwrap, frame/cap/no-hit, concrete delegated rest and source1161, StoredCarrierBinding and release identities remain open. No new probability conditioning, collision term or trust assumption. Both deployed targets not yet established.

Lead independently read helper/consumer/full before-after signatures, checked exact unchanged conclusion, generator --check, all three final source hashes, seven standard-axiom audit reports and caps/swap receipts. Audit005 at0a7aab30af plus exact source/dependency hashes: exit0,1.997596704022726s,peakRSS4463268KiB,swap0. Cached dependencies reused with source/object assessment; no coherent release replay or new ELF gate. Complete host-wide admission scanner and nested/system-Docker/uncapped/missing-data fixtures reviewed and passed; five fresh locked admissions each24.375GiB+8GiB<55GiB. This does not repair historical aggregate evidence.

Budget remains218 actual compiles+1pre-Lean charge=219/220 charged,1slot remaining; Kani0/20. Next scoped worker will inspect and instantiate actual local callback producers/adoption where genuinely sufficient, with a committed dependency assessment before proof work, without duplicating session A prepare/powers/sampler.


## Addendum (lead, 2026-10-24): callback audit; actual driver partition next

Port14LOCAL d297222029 reviewed: callbacks are proof-only comparison witnesses; native parent/leaf accepted physical transport already exists in Port9/10. No callback wrapper or kernel theorem added and no source assumption discharged. Source audit43files/10byte-identicalhistoricalgreenreceipts plus localadmissionfixtures independently rechecked read-only. Full source interfaces and unchanged endpoint statement retained. The all-failD counterexample explains why literal totalParentGate cannot describe failure-preserving nativeproducer; choosing canonicalcomparison witnesses is not nativeadoption. No shipped/security/trust/keychange or formalreplay.

NEXT-PRODUCER.md identifies exact actual TX1/TX2 sites and weighted delegated bound:2*w3+w4+2*w6+w7+2*w9+2*w10+2*w11+w12+w17+w19<=115. Unrestrictedrest can issue1162asks at firstop3 and reject, so full1161 is false without localproducerbounds. Lead next owns proving actualdrivercontrolpartition/all-outcome composition from explicit per-op budget producers, using realreturned savedVec/Prepared and 477+3+3+563=1046, NOT checkpointChainprojection equality. SessionA retains concrete parser/prepare/powers/sampler/primitive bounds; no duplicate work. A conditional partition theorem will close only sourcecontrolcomposition, not concrete115orfullrelease. Budget219/240charged,21remain,Kani0/20; no newLean allocation.

Client64 worker2349 now implements D162 caller migration separately on unmergedcandidate, tools/scripts only with offline mocks; no chain/key operations, crates/programs changes or nativeprivacy/adoptionclaim. NativeDrop386 remainsactive. Bothdeployedtargetsnotyetestablished.


## Addendum (lead, 2026-10-24): actual TX1 control bound; full driver still open

Reviewed Port15DRIVER65ed227d5b and accepted ONLY greenCost/Local/TX1 modules. Port15DRIVER_TX1.tx1 proves actualsplit10/None TX1 all-outcomelog<=480+w3+w4+w7+w12+w11+w10+w6+w9, preservingactualreturns andfailureprefixes,conditionalonexplicitallargument/allHper-operationLocalBudgets. No fullsourcebound/refinement/equalityhiddeninthatdefinition. ConcreteR/weightsandweighted115remainuninstantiated. FullTX2module/stages/rust/1161wereNOTaccepted: failed020/021containheartbeatfailuresandcompiler-generatedsorryAx,retainedoutsideimportedLeantree. TX2standardaxiomsprintedinsidefailedmodulearenotagreenreceipt.

Leadreadall134acceptedsource lines/fullLocalBudgetdefinition and failedcompositioncandidate; independentread-onlyauditchecks3finalsourcehashes,21receipts/admissions/caps/swap,1050reachablelocalsourcehashesand3reusedcapreceipts. TX1lean019at224a0010cb+exacthashes exit0,3.623115777998464s,RSS4454348KiB,swap0,standardthreeaxioms. Rawfailedlogwhitespace retainedverbatim;noartifactrewrites. Cachedfocusedvalidationonly,nocoherentreplay/ELFgate. Historicalaggregatecaveatstillappliestoreusedevidence.

Budget240/240charged(239actual+1preLean),Kani0/20. Leadallocates12newLeanattemptsforstandaloneTX2,explicitlytypedProgramcutsandactualsame-savedVecdrivercomposition,ceiling252. Noheartbeat/recursionraiseorunchangedretry. Actualsourceadoption/parser/prepare/sample/powers/terminalclassifier/nohit/StoredCarrierBinding/releaseidentitiesremainopen. Bothdeployedtargetsnotyetestablished;exactboundunchanged.
