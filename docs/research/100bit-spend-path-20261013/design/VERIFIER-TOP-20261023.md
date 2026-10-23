# Verifier stage-entry assessment — 23 October 2026

Status: unchanged stage bodies extract successfully; S2 remains open. Branch
`codex/cx-verifier-top-20261023`. Receipts are at repository-root
`evidence/verifier-top-20261023/`.

## Frozen scope and intended claim

Assess actual `candidate::tx1`, `candidate::tx2_authenticated` and its
`tx2_common` continuation with cone top functions opaque. Successful extraction
is a prerequisite to source identity and the ordered cone decomposition;
no assumed callback identity will be reported as discharge.

The adapter theorem and the C5 checkpoint writer/resume endpoints are reused
only within their stated premises. No existing Lean module or shipped Rust
source is changed. Release pins and initial source hashes are in `target.json`.

## Validation and remaining obligations

Initial inspection only: zero Lean attempts, zero Kani runs, no new theorem,
no axioms audit, no release build. Target not yet established. Next deliverable:
an admitted capped extraction probe and its exact source/tool receipt, or a
minimal stage-glue restructuring proposal if the probe exposes an obstruction.

## Stage 1: actual stage glue extracts

Charon 0.1.223, built MIR, Aeneas preset, native Linux, release default
private-leaf-salts feature: roots are the exact current `tx1`, `tx2_common`,
`tx2_authenticated`. All other crate and protocol bodies are opaque; reached
value layouts are transparent. No Rust source rewrite, stub body, LLBC
transformation, or borrow-check bypass was used. Charon reports has_errors=false.
The first LLBC is 1,521,015 bytes, SHA-256
`1511b8380f4e5f39d58c23a5ef1d10d2406b951992ec8501e39e1c79e069dff6`.
Aeneas emits all three stage bodies, including every error branch and checked
slice/array operation. Raw output is retained as `.lean.txt`; generated external
axiom templates are *uninstalled tool output*, never accepted Lean premises.
The next extraction includes complete reached layouts to remove external type
holes, then parameterizes external functions as named operation fields.

| Attempt | Exact target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| charon-001 | three actual candidate stage roots | 0 | 81.1184 | 539568 | 0 |
| aeneas-001 | VTop_Stages.llbc → Lean | 0 | 1.0329 | 128656 | 0 |

Both used admitted independent scopes: MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Full commands, environment, source revision,
source hashes, limits and logs are in the respective receipt directories.
`host-overlay.json` pins 540 overlaid Rust/Cargo inputs; all hashes checked on
host before extraction. `toolchain.txt` pins both translator binaries and rustc.
No Lean theorem or op10/op11 installation is established by extraction alone.

## Stage 2: installed source identities and ordered accepted calls

`VTop_Types` shares already extracted Rust value layouts with AdapterRw and
AspisR1Stage2. This is a namespace/carrier adapter, not a new representation
or a cone proof. `VTop_Model` preserves the generated stage bodies and takes
24 generated external operations plus one pure std array-unwrap operation as
explicit `Ops` fields. No generated template axiom is installed. The unwrap
boundary is necessary because the backend's direct `DebugTryFromSliceError`
instance pulls `core.fmt.Formatter` into the axiom set (lean-003, excluded).
The accepted model (lean-004) uses standard axioms only. This boundary remains
part of the existing std/extraction interpretation, not a proved concrete std
instance. Remaining opaque nested public-layout templates are likewise not
installed; their already extracted complete carriers are shared explicitly.

`VTop_Entry.install adapter stage` sets only adapter op10 and op11 to the exact
extracted tx1/tx2_authenticated definitions. `op10_source` and `op11_source`
prove their identities for this installed dictionary, at every hash type and
digest dictionary. They do **not** assert equality of an arbitrary pre-existing
`AdapterRw.Ops` dictionary with this instance. `first_accepted` inverts the
actual adapter error map: its successful checkpoint is the same successful
stage return, with unit hash and observer None. Source span/hash checks in
`source-identities.json` identify all three extracted bodies with this
worktree's `candidate.rs`; they do not establish SBF lowering.

`VTop_Flow` lifts these exact bodies into typed operation syntax.
`VTop_Erasure.{tx1,tx2_common,tx2_authenticated}_source` and `_erasure` prove
full Result equality, including failure/divergence and inner Rust errors.
`VTop_Trace.Call` retains each operation's actual typed arguments;
`Event.returned` retains its actual return. `accepted_execution` derives an
execution trace from source acceptance, rather than assuming successful cuts.
`VTop_Order.accepted_tx1` / `accepted_tx2` derive those same-value traces and
the exact operation schedules below. They are not independent successful
executions selected to fill desired inputs.

- TX1: split guard → shape → canonical scan → Parsed mark → zero scratch →
  preparation (returned scratch included) → initial accumulator → Prepare mark
  → folded-root range/conversion → batch 0 → Merkle mark → geometry → pending
  weights → query loop → weight flush/back-write → checkpoint → write mark.
- Authenticated TX2: shape → Parsed mark → resume → split check → powers →
  read mark → inactive range/decode → folded-root range/conversion → batch 1
  → Merkle mark → geometry → pending weights → query loop → weight flush →
  relation-view construction → finish_relation.

All checked slice calls and pure array materializations remain in the tree.
`VTop_Cuts.writer_reached` and `resume_reached` independently invert acceptance
to the exact writer/resume child invocation on the original proof/public/CP
arguments. They supply no assumed checkpoint encoding or returned state.

The combined TX2-order proof hit the fixed 200,000-heartbeat limit in
lean-023 and, after a first smaller split, lean-030. Neither was rerun
unchanged. `VTop_SecondFlow` factors only the *Lean proof definition* at the
query-return continuation; `common_source` proves definitional equality with
the original monadic body. `VTop_SecondOrder` checks the four-operation tail
and the prefix separately (lean-032); the authenticated wrapper then composes
them (lean-033). No Rust/LLBC rewrite, cap or heartbeat increase occurred.

**Task (2) is partial:** source identities and accepted typed call order are
proved. The complete `OraclePortFrozen2Join.AcceptedRunJoin` observation is
not proved. An operation-return log is not a digest-query log. No theorem here
claims equality to `verifier D dV_frozen2`, equality of its two enriched
annotation passes, or inhabitants of the thirteen `PerConeJoins` fields.

## Stage 3: conditional checkpoint endpoint installation

`VTop_Checkpoint.writer_join` / `reader_join` use the accepted-stage cuts and
the *existing* `ChildJoin_Checkpoint.writer_header` / `reader_header` proofs.
They derive both adapter checkpoint contracts for `install adapter stage`.
The decoder stays the fixed C5 `checkpointHeader`. No `S2CallerFacts`, saved
encoding, independently chosen checkpoint, hash injectivity or checkpoint
persistence is used to manufacture these headers.

The exact retained premises are deliberately visible:

- `CheckpointSourceJoin.writer`: a successful stage writer call preceded by
  the actual successful `WriterPrefix` transports to the existing writer effect
  program, with namespace-converted Prepared and Accumulator, the same
  proof/public arguments and actual returned bytes.
- `CheckpointSourceJoin.reader`: every successful stage resume call transports
  to `resumeWithOps (CheckpointBytes4Ops.ops reserved)` on the same checkpoint,
  proof/public inputs and returned Prepared/Accumulator.
- Per-call digest/oracle interpretation, with fields copied between the two
  extracted Digest32 namespaces.
- `WriterProvenance`: the original `S1S7S8StateProvenance` for namespace-converted
  writer state, conditional on the successful `WriterPrefix`. That prefix
  contains the actual split guard, shape/scan, zero scratch, preparation branch,
  initial accumulator, batch, geometry, pending, query-loop and flush equations
  on the same raw fields. It contains no checkpoint output or encoding fact.
  `VTop_Provenance.writer_prefix` derives it and the exact writer call together
  from stage acceptance. Provenance itself remains a named S1/S7/S8 obligation.

The initial uniform proposal in lean-020/028/034 was too strong: applying
canonical reached-state provenance (and fixed-S2 serialization transport) to
all successful arbitrary-state writer calls is not justified for the concrete
writer. That proposal and its earlier union audits are superseded, with no
closure credit for this overbroad interface. The final interface is restricted
to the source-derived prefix. A first search-based prefix inversion timed out
in lean-038; the replacement selects existing typed witness equations directly,
then checks their conjunction (lean-045), without raising limits.

`VTop_Accepted.accepted_run` specializes `ChildJoin_Accepted.accepted_run` to
this installed dictionary and replaces its two header-contract continuation
arguments by these endpoint applications. It retains checkpoint source
transport and oracle interpretation as top premises and WriterProvenance in
the continuation. The complete Required14 conclusion, reached-site relation,
native wrapper execution/frame outputs, physical range child joins,
checkpoint-version history, P2Prime, runtime/SDK/std/allocator/extraction and
syscall premises are retained verbatim, specialized only to the installed
dictionary. It does not use or add FullForestAcceptedRoundtrip.

Before: arbitrary adapter dictionary, fixed decoder, independently supplied
CheckpointWriterConeJoin and CheckpointReaderConeJoin, then Required14.
After: the explicitly installed stage dictionary, successful source endpoint
transport, oracle interpretation and prefix-indexed state provenance, then the same
Required14 conclusion. This proves **conditional endpoint composition**;
it is neither unconditional removal of checkpoint source refinement nor a
proof that the new source-transport premises hold for the frozen children.

## Exact outstanding obligation and handoff

The requested full observation part of task (2), and therefore unconditional
task (3), remain open. To reach the original JOIN-SPLIT target, instantiate a
concrete release-specialized Signature, source/model Implementations, S10
inventory and caller tree from the typed stage calls; provide the thirteen
named per-cone refinements on those *same* carriers. In particular:

1. S1 must identify the actual prepared state, gamma scratch and preparation
   digest continuation with the reached transcript/parser/query state; the
   source-call order theorem does not identify these mathematical values.
2. Parser/compact, S7 and S8 must transport their actual returned raw fields,
   geometry, pending weights and flush result into that reached model state.
   S3/S4/S5/S6/S9 remain their owners' child dependencies, not new assumptions
   silently hidden in an S2 proof.
3. Multiproof must bind `stage.op5` to the physical batch source program, with
   its ordered child reads and byte views. Checkpoint must instantiate the two
   `CheckpointSourceJoin` source transports; endpoint header proofs alone do
   not supply either transport.
4. Substitute these concrete child observations into the extracted typed tree
   and prove its model interpretation equals `verifier D dV_frozen2`, including
   returned state, both annotation passes and enriched outputs. The full
   model-order identity is not an added hypothesis in any new theorem here.

This packet does **not** replace thirteen open joins by one assumed whole
verifier equality. It also does not report typed event IDs as physical oracle
reads. No new security conclusion, trust ruling or source adoption is proposed.
There is no extraction-driven need for a Rust stage-glue restructuring at this
boundary; no such rewrite or CU estimate is required. Shipped code and its CU
are unchanged by construction; no new CU measurement is claimed.

## Validation, pins and final resource receipt

Final focused union: `VTop_Audit.lean`, lean-049, exit 0, wall 3.166975 s,
peak RSS 4,390,696 KiB, swap 0. It imports the accepted-run specialization
and both stage-order paths, prints all public new theorem axiom sets and the
complete final checkpoint/source/provenance interfaces. Every accepted new
theorem uses only a subset of `[propext, Classical.choice, Quot.sound]`.
Private helper `bind_congr` is independently audited in lean-015 (Quot.sound).
Raw compiler-recovery sorryAx output and lean-003's Formatter-dependent model
are retained as excluded historical evidence; no such premise occurs in the
accepted sources or final union audit.

Budget consumed: **48/100 actual Lean compile attempts, 0/60 Kani runs** (49 allocated IDs, including the compiler-free preflight).
Configuration lean-010 was a missing-source generator/setup failure and
launched no compiler; it is separately recorded. Both deterministic heartbeat
failures are retained with their source hashes and the subsequent source splits.
No wall timeout or memory kill was rerun unchanged. The maximum process RSS
across all jobs was 4,408,248 KiB; every receipt reports zero swaps.

Every compile was one changed/split module with `lake env lean -j1 -M4400
-DElab.async=false` on the host, with private objects, admission below the
55 GiB reservation ceiling, and the shared global Lean lock. Every extraction
and compile had its own scope: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. Charon used native Linux default private-leaf-salts, `aeneas_ref`,
optimized release dependencies and one compiler job; exact flags are in JSON.
`manifest.json` records every command/target receipt, revision, final source
hash, direct dependency fingerprint, exit, wall, RSS, swap and complete axiom
lines. Source revision for the final focused audit is `addab0ff67` plus the
exact dirty-source hashes in its receipt. Old compiled dependency closures
were reused read-only; this is **not a coherent H5 frozen release replay**.

The packet audit (`python3 tools/verifier-top-20261023/VTop_manifest.py`) checks
all receipt source hashes, fixed caps, final-source accepted compile coverage,
standard axioms and unchanged initial shipped-source pins. The source-span
audit (`VTop_source_audit.py`) independently checks Charon source text against
the worktree. These inspections launch no Lean, Rust or solver process.

No shipped source, existing Lean module, other worker's candidate, worktree,
wallet/key, wire parameter or security contract changed. The source parameters
remain compact proof 57,607 bytes, checkpoint 1,768 bytes, split 10/12 queries.
No SBF/ELF or runtime suite ran; the three-ELF rebuild trigger did not fire.
The C3-BIN 18:15 release pins remain default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
Pool `121f3e29…`; they were **not independently rebuilt/reconfirmed here**.
No full frozen manifest replay was run for this additive, conditional packet.
Target not yet established; the next substantive deliverable is the concrete
per-cone oracle/state interpretation and frozen2 model-order proof above.


Final housekeeping: trailing whitespace was removed from the generated typed
trace without changing its tokens (lean-036), and the audit pins that object
directly. Authored module/tool/report whitespace checks pass. Raw compiler
logs and historical exact source snapshots retain their original whitespace.
The final manifest excludes the superseded uniform checkpoint interfaces and
their union audits from accepted final evidence; lean-047/048/049 establish
the corrected prefix-indexed interface. No source or proof job remains live.

## Continuation stage 4: audit of the requested endpoint's inputs

The requested `AcceptedRunJoinFromCones` and deployed theorem are **not yet
established**. The intended concrete construction is legitimate, but cannot
be replaced by an implication for an unbound `rust : Verifier`.
`S2W_DigestExtraction.AeneasExtraction` contains only native/owned `Result`
identities and the digest source identity. Neither it nor Required14 binds
`OraclePortRuntimeBindingC7.Verifier` to an oracle interpretation of the
extracted typed stage tree. `ChildConeJoin.erasure` likewise determines
returned values, not the meaning of its generic event carrier as ordered
oracle reads. This is a missing construction/proof, not a new trust item.

`VTop_ObservationBoundary.extraRead_value` / `extraRead_observation` formally
show that even a complete returned state can stay identical while the oracle
observation changes. `no_unbound_verifier_join` gives an explicit unrelated
always-accepting 1162-read verifier that cannot satisfy the frozen2 join,
using the existing 1161-read budget. This is **not** a counterexample to the
actual extracted verifier or to the intended fully instantiated composition;
it rules out inferring an arbitrary headline verifier's join from the
value-only interfaces. In particular it does not refute future cone laws
that explicitly bind the concrete oracle interpretation.

Focused validation: lean-050 failed on two list-length elaborations; the
changed symbolic list proof passed in lean-051 (exit0, 2.170872s,
4322964KiB RSS, swap0). Every new theorem prints only standard axioms.
Exact source revision, hashes, dependencies, command and cgroup limits are
in `evidence/verifier-top-20261023/lean-05{0,1}/receipt.json`.
No release claim, new runtime assumption or shipped-code change is made.

## Continuation stage 5: typed oracle substitution

`VTop_OracleCode` gives the already extracted `VTop_Trace.Code` an explicit
oracle interpretation, including outer Aeneas failure/divergence and ordinary
inner Rust rejection. A call consumes its original dependent arguments and
returns its complete dependent state. `accepted_interpret_eq` proves local
accepted-return observations substitute through that syntax, with exact
ordered read concatenation and branch selection. Its only local law is
`CallJoin`; no whole-verifier/model-order identity appears in its statement.

This is a composition mechanism, not an instantiation of the frozen source
oracle semantics. Its local success condition is outer Aeneas `ok`; inner
Rust `Err` remains a returned value, so this mechanism's local law covers it
as well. It must not be advertised as the weakest accepted-inner-run cone
interface. The theorem checks in lean-052: exit0, 2.152566s, 4332744KiB RSS,
swap0; standard axioms only, exact target/dependencies/revision in its receipt.

## Continuation stage 6: named actual call-site ports

`VTop_OracleStages.ConeJoins` names the thirteen external *body* operations
reached by the extracted stage glue. This is not the thirteen-owner enum of
JOIN-SPLIT: S3/S4/S5/S9 are nested inside these bodies. The separate `library`
field covers the twelve remaining generated operations/constants. `all_calls`
proves this inventory exhaustive by cases on the actual dependent `Call`.
`accepted_tx1`, `accepted_tx2_common`, and `accepted_tx2_authenticated` apply
ordered oracle substitution directly to each extracted typed stage tree with
observer None. They compare the two supplied interpretations; neither is yet
identified with the source ROM execution or the corresponding frozen2 model
stage. There is no assumed caller/model-order identity in these theorems.

Focused validation lean-053: exit0, 3.361611s, 4340500KiB RSS, swap0;
all four theorem axiom reports are standard. The `OperationJoin` law is still
outer-success conditioned, including inner errors as values, as explained
above. None of these new ports is claimed discharged merely because its
owner has a local helper theorem. The following table is the concrete
**remaining delivery inventory**, not the premise list of a proved deployed
soundness theorem. Owner means coordinating owner in the lead/session-A
split; it does not transfer another worker's worktree or certificate.

| Named body port / actual call site | Owner | Existing result and exact gap to a frozen2 observation |
|---|---|---|
| `shape` / op3, TX1 and authenticated TX2 | lead | `S2W_ChildJoins.FirstEntryVerifierConeJoin`, `OraclePortJoinSplitS2.header_total`: physical size/header facts; full `parseReached`/transcript correspondence still needed. |
| `scan` / op4, TX1 | lead | `S8JoinFrozenScan.parsed_y1`, consumed by `S2LeadInterface.y1_join`: selected y1 canonical scan; full source `canonical_scan` accepted interpretation still needed. |
| `prepare` / op7, TX1, returned gamma scratch included | session A | `AspisR1ClaimPreparedBridge.InstalledMeaning.prepared_installed_meaning`: local successful preparation meaning; bind the actual returned Prepared, scratch, full transcript driver reads, parser and queries. S3/S4/S5/S9 are dependencies here, not separately ordered top-stage calls. |
| `initial` / op12, TX1 | lead | `S7JoinQueryRows.initial_progress`: row-state initialization only; identify complete initial accumulator and state conversion. |
| `batch` / op5, batch0 TX1 and batch1 TX2 | lead | `S2LeadInterface.multiproof_join`, `MultiproofConeP6Frozen2Stage.both_batches`: ordered frozen2 batch join at supplied physical callbacks/node views; bind actual `candidate::batch_merkle` operation and returned/error semantics. |
| `geometry` / op11, both query blocks | lead | `S7JoinQueryRows.query_rows_exact` consumes query/cadence bounds; actual `QueryGeometry::for_range` result and both ranges still need interpretation. |
| `pending` / op10 of **stage** dictionary, both blocks | lead | `S7JoinQueryRows.initial_progress`, `S7Kani3CallerTrace.initialRaw`: row representation; bind actual `BatchedWeights::new` and complete returned state. This is distinct from adapter op10. |
| `query` / op6, ten and twelve steps | lead | `S7JoinQueryRows.query_rows_exact` / `initial_query_rows`: basis/64-row/terms part only; full source loop, opening/fold, rhs/power/next and state to `advance` remain. |
| `flush` / op9, both blocks | lead | `S8OwnedP6Finish` and `S7Kani3CallerTrace.reached_invariant`, consumed by `S2LeadInterface.compose`: local raw/caller algebra; identify actual finish and Vec back-write state. |
| `writer` / op8, after ten steps | lead | `VTop_Checkpoint.writer_join` and `CheckpointBytes5Join.success_conditioned_checkpoint_stage_join`: header and full checkpoint composition respectively, conditional on source transport and reached state provenance. Bind actual op8 ordered reads/bytes and reached mathematical state; header alone is insufficient. |
| `reader` / op18, TX2 resume | lead | `VTop_Checkpoint.reader_join`, `ChildJoin_Checkpoint.reader_header`, `CheckpointBytes5Join.successful_fields_and_reads`: conditional source/physical-byte endpoints; bind actual op18 full returned Prepared/Accumulator and retained same checkpoint. |
| `powers` / op17, TX2 | session A | `AspisR1LoopPowers.early_powers_total_exact`: canonical-input power result; actual resumed gamma, full array and no-read interpretation remain. |
| `finish` / op19, TX2 | lead | `S8Kani2CallerJoin.CallerInvariant`, `OraclePortFrozen2.finish_value`: source invariant/model finish separately; actual `finish_relation` on returned twelve-step state must bridge them, including S3/S4/S5/S9 dependencies. |
| `library` / ops0,1,2,13–16,20–23,unwrap32 | lead | Existing TrustedStd/extraction carries ordinary library semantics but does not instantiate this new oracle law. Pin constants, strict decode, release observer None and exact no-read implementations; do not silently add it as runtime trust. |
| Nested S3/S4/S5/S9 backend refinements | session A | JOIN-SPLIT table's grouped-pair/dot/strict-codec/reducer/factored identities; complete parent-body instances, reached operand bounds and source pins still required. |
| S6 first-decoded/semantic/public input transport | session A | `AspisR1PublicPreparation.RepinS6First.{first_eq_historical,first_success,reuse_decoded}`; actual downstream cone instances and source/byte carrier binding remain. |
| S2 adapter/native input and frame facts | lead | `S2W_D189Consolidation.accepted_run`, `ChildJoin_Accepted.accepted_run`, `VTop_Accepted.accepted_run`: complete Required14 under their explicit runtime/trust/history/child premises, not a headline oracle-program binding. |
| Cross-TX checkpoint and Pool/ASQ8 retention | lead | D189's `CheckpointVersionBinding`/`P2Prime` remain explicit. No hash-injectivity or independently selected byte snapshot is introduced. Pool caller remains outside these stage bodies. |
| S10 source/inventory/artifact correspondence | session A | `VTop_Order` fixes stage call order; source-span audit fixes source identity. Neither proves lowering to the pinned ELF; current declaration coverage and artifact/runtime port remain. |
| Actual headline `rust` binding and substituted model order | lead | Newly explicit typed interpreter and stage substitution above. Still construct the source verifier/decoder/transcript driver on these carriers, and prove its substituted interpretation is `verifier D dV_frozen2`; no existing theorem closes these identities. |
| Both annotation passes | lead | Existing `acceptedRunJoin_of_stable` is sufficient only with an independently proved source enrichment law. The new `VTop_Annotation.two_pass` uses just backward acceptance plus raw join; that source backward law is still uninstantiated. |
| Deployed runtime carrier / query budget | lead | `StoredCarrierBinding D rust P runtime` and `hqueries` remain independent premises of `OraclePortHeadlineFrozen2PerAttempt.final_soundness`; D189 alone does not discharge them. |

The checkpoint combined model observation advances the twelve pure arithmetic
steps before returning to batch1; extracted TX2 executes batch1 before those
steps. A completed model-order proof must justify this transport from the
query/flush no-read laws and returned-state equations. Neither operation-ID
order nor an equality of checkpoint headers establishes it.

No `AcceptedRunJoinFromCones` or deployed endpoint with the requested exact
premises is claimed. Adding `h_source`, `h_model`, `stable`, an arbitrary
whole-run certificate, or these claims inside a record would not complete
that request. The next missing declaration is the concrete interpretation
of the native two-stage execution as the headline `Verifier`, followed by
its model-order proof with these per-call stage observations. This is still
lead-owned proof work, not an additional cryptographic assumption.
