# L1 native observation inputs — D456

Final partial handoff. Branch `codex/pv-l1c-20261029`, base `f2caad8ab2`.
The four concrete native producer obligations remain open. New compositional
model lemmas do not supply native producers or remove endpoint premises.

## Boundaries

No changes to crates, programs, runjoin definitions, observer or simE.
No new trust item. No wallet/key operations. D359 timing evidence is pending.

## Final per-input classification

**All four are PARTIAL; none of the concrete native input instances is proved.**
The exact requested types are unchanged in `lean/PV_RJ4IDB_OpenInputs.lean`.
Here `I` ranges over all admitted paths and finite prefixes, including prefixes
of rejected attempts, failure, panic/abort and divergence; no success restriction
or new witness predicate is introduced. `native : I → PV_RJ4IDB.NativeTrace A`.
The `actual*` functions must be supplied by the deployed execution, not defined
as the decoder's own projections to obtain reflexive proofs.

| Input and exact outstanding statement | Proved part in this job | One named remaining obligation |
|---|---|---|
| `PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native`, i.e. `∀ i, actualCount i = (nativeCounts (native i).events, nativeRejections (native i).events)` | `PV_L1C.count_splice`: exact typed composition of independently associated sequential stages on the SAME index. `counts_append`/`rejections_append` preserve entered and rejected prefixes. Source inspection binds the spellings of returned count/account/upload fields to the same `result.attempts`; it is not a complete source refinement. | **L1C_COUNT_NATIVE_JOIN**: construct the native producer on the original D163 experiment, associate its whole retry/callback/body prefix with the D163 owner, and derive the joint simE law for successful count, V394 account, proof length, uploads and operation counts, retaining original failures. |
| `PV_RJ4IDB.OpenInputs.L1_TIME_TRACE actualTime native`, i.e. `∀ i, actualTime i = nativeTimes (native i).events` | `PV_L1C.time_splice`, `restore_times`, `timing_key_injective`, `timing_extension_iff`, `same_bad_event_agreement`; exact-law criterion `timing_law_iff_tests`. Actual timing bytes are retained, never replaced by a constant. | **L1C_TIME_NATIVE_KERNEL_D359**: associate native `Instant::now/elapsed/as_secs_f64` and serde JSON formatting, and supply the joint timing/noise law on the original experiment, ordered context and failure event. Owner **D359, timing-evidence decision for measurements on a throttled host, is pending and not assumed**. |
| `PV_RJ4IDB.OpenInputs.L1_ORACLE_PREFIX actualOracle native`, i.e. `∀ i, actualOracle i = nativeOracle (native i).events` | `PV_L1C.oracle_splice`, `oracle_append`, `duplicate_failure_prefix`, `terminal_does_not_erase`: arbitrary ordered prefixes and repeated identical address/answer pairs survive composition and terminal failure/divergence. | **L1C_ORACLE_NATIVE_LOG**: bind EVERY native ROM observer query/answer, duplicate, rejected-attempt and failing/diverging prefix to the source-world call log, including effects inside callees. |
| `PV_RJ4IDB.OpenInputs.L1_RETAINED_SIDECHANNELS actualSide native`, i.e. `∀ i, actualSide i = nativeSide (native i).events` | `PV_L1C.side_splice`/`side_append` preserve the full named payload word. `four_inputs_do_not_fix_order` proves that the four projected equations alone cannot supply cross-channel order, even at the same failure terminal. | **L1C_RETAINED_NATIVE_WORLD**: associate native allocation/address/physical/durable/environment payloads and their interleaving with the same original failure coupling, consuming the ownership/world interface at each reached continuation. |

The splice hypotheses are the exact two still-open stage producer equations;
they are NOT evidence that those equations hold for the client. These theorems
are mathematical/model progress only. No new concrete native producer, native
honest execution witness, native count law, timing measurement, extraction or
structural source-binding certificate was obtained.

## Original experiment, counts and timing

D163 is reused at its established scope: `SideChannelL1AttemptRecord.erase_run`
retains retry control and state; its rejected/stopping/success prefix laws retain
records; `SideChannelEntropyLaw.first_accepted` and `sixteen_exhaustion` concern
the IDEAL IID two-seed/all-Ok draw law, not geometric outer prover retries.
`SideChannelRetryLaw` supplies history-conditioned hazards without an IID
retry assumption. These existing sources/reports were reviewed and retained;
they were not rebuilt or instantiated with a native producer in this job.
No new marginal count experiment replaces them.

The parked pv-l1 handoff remains authoritative about its limits:
`PV_L1_EntropyProducer.source_replay` and `PV_L1_EntropyCounts` retain the
source-tape status/count; `PV_L1_QueryRecord.of_source/abort_record/digest_count`
retain seventeen digest ENTRY tags on completed source results, including inner
Transcript errors. They do NOT contain every native query address/answer or
cover an outer incomplete call by pretending that it completed. Source069's
full-body tail, Source071's retry erasure and the Source020 double-Logged lift
are still parked, unaccepted drafts. No native credit is borrowed from them.
V163 native body/data and V167 native effects stay explicitly open.

`source-audit.json` records exact revision/blob/SHA and source sites for three
client roots. At `plan.rs:117`, selection consumes `result.attempts`; the selected
policy checks count in 1..=8 AND equality to entered callbacks, then uses
`attempts-1`. Publication consumes the same count. The returned JSON uses
`result.attempts`, proof length's `div_ceil(3763)`, and one statement upload.
This does not prove their honest joint law or a fixed number of all operations.
Selected account belongs in retained JSON/side observations, not an invented
extra meaning for `nativeCounts`. Byte/upload sizes require the same published
proof bytes, not an independently simulated length.

The exact serialized timing includes the call to `Instant::now` BEFORE note
and witness preparation, followed by preparation, durable recovery/nonce-store
work, retrying proving, account selection, proof/statement writes and account
construction before `elapsed().as_secs_f64()` inside the returned JSON.
Consequently prover instruction-count equality alone cannot establish this
client timer's law. JSON serialization, stdout formatting/allocation/delivery,
all other retained timing observations and terminal failure remain in the
observer. Clock/environment reads disqualify the client from own-2'''.

For the unchanged D163 proof method the sufficient timing obligation is a
JOINT extension of the SAME original coupling and SAME charged bad event:
whenever the original good samples' ordered non-wall context and terminal
agree, couple the retained timing word so that it too agrees. Native scheduling
noise may be coupled; identical wall time at identical seed inputs is not
asserted. `PV_L1C.timing_extension_iff` gives the precise pathwise remaining
condition once that context agreement is established;
`same_bad_event_agreement` returns the `agree` shape consumed by D163's
`SideChannelL1JointCoupling.dist_le_bad`, with no new failure charge. Neither
its native context premise nor its native timing premise is supplied here.

More generally the needed claim is the original full JOINT observation distance
bound against simE, including failures, after timing is retained. Exact equality
of joint laws is a sufficient stronger alternative, characterized for finite
uniform carriers by `JointTimingLaw` and `timing_law_iff_tests`; it is not claimed
necessary for an already statistical privacy bound. Those finite-carrier
lemmas do not assert that native OS timing has a finite uniform law.
`timingKey` is lossless: it retains wall-event positions, every other event and
the terminal, plus the exact wall bytes. In particular returned JSON and timing
payloads in side channels stay intact in its context; the context hypothesis is
NOT silently made public or assumed already proved by the count model.

D359 is precisely the pending owner decision about timing evidence obtained on
a throttled host. No measurement from that host was adopted, no new measurement
was run, and no empirical test was promoted to a universal timing law. Existing
compiler/CPU obligations V370/V371 and pending D381/D386 are retained.

## Retained world and influence boundaries

Reuse **rdea-1** as stated in `evidence/pv-rdea-20261028/REPORT.md`: the existing
runtime/allocator primitive adequacy item covers success/failure and the
failure-selected prefix on public-sized planned request words, including prior
allocator state. It is not a new witness-independent allocator-state hypothesis.
`PV_RDEA_V181ConsumedLaw.consumed/name_stage` retains the actual failure
continuation/post-world and one `(0,69,1)` name allocation request; the companion
V178 law retains join failure prefixes. These size-word results do not erase
addresses, errors, memory or histories and do not prove public provenance of
all client allocation arguments or diagnostics. No new failure-event exemption
or successful-allocation premise is introduced.

Reuse the **pv-own** interface rather than a logical-cell replacement:
`PV_OWN_Reserve.complete`, `initialized_prefix` and `typed_prefix` retain the
complete reserve outcome and initialized-byte association;
`PV_OWN_Containers.VecView/StringView` distinguishes zero capacity and UTF8;
`PV_OWN_WorldAdapter` retains process fields. These interfaces expose the native
byte/ownership/cursor/drop and continuation associations still needed by
L1C_RETAINED_NATIVE_WORLD. This job read and relies on their documented scope;
it does not claim to have instantiated or freshly replayed that cone.

Under **own-2'''**, memory primitives confined to supplied arguments stay at
V370. The allocator's influence channels remain success/failure (rdea-1),
returned addresses, and state it writes that a later callee reads. No blanket
input-free classification is applied to a witness-bearing prover or to a
client that reads the clock, files and environment. No singleton-domain harness
claim is made. Under **own-1**, a class-B source binding requires every deployed
source control step/store/drop/error/abort branch; no LLVM/machine-level
correspondence is demanded in its place. The V370 D381/D386 boundary remains.
No new b3p6-1 token-identical body reclassification is claimed: this job ran
neither a macro-expanded token comparison nor a pinned extraction/hash-chain
check. No Kani, copy-dependent PASS, Option<fn> PASS, XR model, or altered trust
field was consumed.

## Combined statement and before/after

`PV_L1C.PendingNativeInputs` is exactly the conjunction of the four original
Props on the SAME `I` and `native` family. It has no instance; packaging those
Props removes no premise. `PV_L1C.combined_observer_law` proves the conditional
model statement, for arbitrary finite sample carriers S and T:

```lean
JointTimingLaw real sim →
 R0Z.EqualLaws (fun s => PV_RJ4IDB.nativeObservation (real s))
   (fun t => PV_RJ4IDB.decoder (PV_RJ4IDB.modelTrace (sim t)))
```

The antecedent is unproved for the actual prover and simE. The alternative
`same_bad_event_agreement` preserves the original bad event instead of assuming
unconditional equality. Neither theorem closes the deployed privacy theorem.

`four_inputs_do_not_fix_order` has two nonempty two-event traces with the SAME
failure terminal, count/time/oracle/side projections, and different ordered
observations. It is a checked countermodel to inferring order from projected
component inputs, **not** an honest-native counterexample or a leak finding.
Its empty illustrative timing bytes/oracle projection are not installed as
native values or failure decoders. Duplicate-query and arbitrary-terminal
lemmas keep earlier prefixes. No honest-run witness-dependent native channel
was established; this is not a proof that no leak exists.

Before/after: V347–V351 remain OPEN/P. V394's source/fixture evidence stays at
its existing scope, with universal native effect coupling retained. The four
D456 producer inputs remain open, with the named blockers above. Headline and
deployment premises removed/added/weakened: **0/0/0**. T stays exactly
`entropy_law`, `entropy_kernel`, `observation`; the failure event, witness domain,
observer and simE are unchanged. **Target not yet established.**


## Verification and AGENTS section 6 receipts

The exact commands, module targets, source revisions/blobs/SHA256s, dependency
fingerprints, exit statuses, wall times, peak RSS, swaps and complete axioms
lines are committed in `receipt-ID.json` and `modules-ID.json`. Original
per-module compiler output and GNU time logs are `raw-ID.output` and
`raw-ID.time`, fetched and hash-checked against their original host receipts.
Final source/object/dependency checks are in `final-validation.json`.

| Attempt | Exact target | Exit | Module wall seconds | Peak RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|
| 65497 | `PV_L1C_Statements` | 0 | 1.01 | 2491809792 | 0 |
| 65498 | `PV_L1C_Axioms` | 0 | 0.97 | 2489696256 | 0 |
| 65499 | `PV_L1C_FocusedReplay` | 0 | 0.95 | 2491416576 | 0 |

All three final audit targets use exact source revision
`59fe34f815` (the full hash is recorded in each receipt). `PV_L1C_Statements`
prints the twenty theorem signatures and the exact four original input types;
`PV_L1C_Axioms` audits all twenty new theorems and reused native_factorization;
`PV_L1C_FocusedReplay` imports that final closure once. Accepted theorem axioms
are subsets of **propext, Classical.choice, Quot.sound** only. Failed compiler
output containing elaborator-generated sorryAx is preserved and earns no credit.

**13/100 Lean compiler starts: nine pass, four fail; nine final accepted
modules; twenty new model theorems. Zero native scopes, zero Kani.**
Attempts are 65400–65409 and reserved audit IDs 65497–65499 only. Each attempt
compiled one module. Maximum module peak RSS 2,501,394,432 bytes, aggregate
module-command wall 8.75 seconds, swaps zero. Four small proof failures were
changed before retry: beta reduction in splice; symbolic tail matching in
timing reconstruction; then two indicator/Decidable-instance mismatches.
No memory kill, timeout, unchanged retry, admission refusal, transport outage,
or ruling-(t) slip occurred. The immediate admission check and launch are in
the same fail-closed shell command; both allowed:true and zero admission exit
are required. ID audits found no other-job receipt or sent-table collisions.
All scopes used 6G/8G/swap0/TasksMax64 and Lean -M7000, one scope at a time.
No local Lean compile, cold dependency build or package/full frozen regression.

Before compilation h6 verified the selected inherited source/object/dependency
cohort, exact Lean githash and inherited LEAN_PATH; h4 verified all 5,673 external
objects. The final required import set has fifteen inherited project modules
and forty-two recorded edges. The selected source bytes equal their retained
cohort records; no stale EJR/proof-only exception was needed, so h5'' did not
license any substitution. No external object was rebuilt, no shared or other
job source/object was written, and the runjoin branch remained read-only.
`source-audit.json` is source inspection, not deployed-feature/build evidence;
therefore no deployed Rust body receives native association credit here.

The exact worktree/branch/base are as requested; sparse paths were added with
`git sparse-checkout add`. No new file exceeds 20 MB; no binary/object is
committed. No crates/programs, protected soundness file, native definition,
wallet/key, other worktree, simulator or observer was changed. No push or merge.
`COMMITS.txt` records the proof-stage `git log --oneline f2caad8ab2..HEAD`;
subsequent commits contain only final receipts/reporting.

## Stop and next concrete deliverable

This is a PARTIAL/OPEN handoff under the requested per-input classification,
not a budget-exhaustion claim. 87 Lean slots and all native slots remain unused.
The concrete items stop at the four named producer/coupling blockers above;
more unconditional list lemmas or timing samples cannot supply those missing
native associations or the pending owner evidence decision. No checked native
witness-dependent finding was obtained. No claim is made that the D456 target
has been completed.

Next: construct the complete original-input native retry/body/world event
producer through `prove_for_proof_accounts`, preserving every earlier callback,
query/answer and terminal prefix, and connect that producer to the D163 joint
experiment. The existing Source069/071/020 parked gaps must not be bypassed by
phase tags or returned-Result projections. Then derive the actual successful
count/account/proof-length/upload/operation fields on that SAME experiment.
For timing, obtain the D359 disposition and the scoped native clock/serde/noise
law; for retained effects, instantiate the existing pv-own/rdea interfaces at
actual native continuations and prove their source/public provenance. Only
then can the four exact concrete Props and the full ordered joint law be
installed and the endpoint premises reconsidered.

`cache-cleanup.json` records post-verification removal of only this job's
rebuildable `PV_L1C_*` compiler objects/IR companions. Original host sources and
compiler/time receipts remain; inherited read-only caches and all wallet/key
material were untouched. `final-validation.json` hashes describe the verified
objects before that cleanup. No additional compilation was run afterward.

The splice lemmas concern raw event-word concatenation, with the right terminal;
they do not assert that a program resumes after a failed left stage. Native
success/failure continuation and world compatibility must be proved by the
missing producer before applying those algebraic equations to an execution.
