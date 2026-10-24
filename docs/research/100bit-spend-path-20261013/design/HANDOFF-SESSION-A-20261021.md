# Handoff to session A (S-cone re-pins), 2026-10-21

From the lead coordinator. Short version: the soundness headline changed this
morning, and it now asks for something specific and narrow from each S-cone
re-pin.

## What changed

The user approved the oracle-decision port. The headline soundness theorem is
now `OraclePortHeadlineFrozen.final_soundness`
(`lean/OraclePortFrozenOrderHeadline.lean`; addendum "oracle-decision port
ADOPTED" in `design/C3-BIN-20261021.md`). Its only source premise is
`AcceptedRunJoin D rust`: on every run the frozen Rust verifier accepts, its
oracle log and outputs equal those of `dV_frozen`, the Lean model of the
frozen verifier, with the exact frozen multiproof order.
`design/JOIN-SPLIT-DRAFT-20261021.md` proves that this join follows from
per-cone joins plus one ordered caller join.

## What each re-pin should deliver

For each cone you own (S1–S6 and S9 per the user, 2026-10-21; the lead has S7, S8, S10, parser, multiproof, checkpoint ABI and Pool caller), the target is an
**accepted-run refinement against the matching `dV_frozen` stage**: whenever
the frozen function returns successfully on the reached inputs, its result
(and any oracle reads) equal the model stage's. The exact statement shape for
each cone is in the join-split table, and `design/CONE-AUDIT-20261021.md`
classifies what already exists and how close it is. The audit ranks S9 and S3
among the cheapest three to close next; the lead is doing the third, the
checkpoint ABI, plus the parser and multiproof cones.

Please state the refinements in **total form** where you can: for every input,
the extracted function returns `ok v` and v equals the model. Then overflow
freedom (R22) for that cone follows automatically from the lemma in
`design/R22-TOTAL-20261021.md`, and no separate overflow census is needed.

## Integration items

- **Combined import.** Duplicated `instDiscriminantErrorIsize`-style instances
  across separate Aeneas extractions block one aggregate import (10 duplicate
  names; three conflicting). A type-qualified naming fix is prototyped and
  shown to compile all cones together (`design/IMPORT-UNION-20261021.md`). It
  needs the S10 pins updated before the single final manifest replay.

## Two things the lead did that touched your work

1. Commit aab0d23d0 (2026-10-20 ~22:40, "Record R19 discharge…") swept in 23
   of your staged files from `lean-candidates/s5-p6-serializer-kani-v1-20261020/`,
   because we share the root checkout's index. Nothing was lost or altered,
   and your later commits build on them. Authorship is yours; the lead now
   commits with explicit paths only.
2. At about 09:33 the lead killed local ssh PID 33838
   (`ssh … echo <base64> …` writing a script for
   `project-offloads/s5-charon-selfid-repair-v1`). It had been hung since the
   ~08:12 network drop, with nothing running behind it on the host. Your
   separately started build-v5 run was not touched. If something was waiting on
   that command, please rerun it.

## S10 ownership lists for your acceptance (added 11:20)

S10 pass 2 assigned every reachable declaration of the frozen verifier and
Pool to a cone. The declarations it assigned to your cones (S1–S6, S9) are
listed in the S10 evidence (`evidence/s10-inventory2-20261021/`, see
`design/S10-INVENTORY-20261021.md`), with 57 ownership corrections. Please
review the lists for your cones and confirm or correct them. Your proved cone
joins should cover exactly those declarations.

## Target update (13:05)

The model now covers both transactions. The headline is
`OraclePortHeadlineFrozen2PerAttempt.final_soundness`, and its
`AcceptedRunJoin` is stated against `dV_frozen2`: stage 1, checkpoint save,
then Pool stage 2, with the six checkpoint digest reads in place. The
per-cone targets for S1–S6 and S9 are the matching stages of `dV_frozen2`.
For the non-checkpoint stages these are the same as the `dV_frozen` stages,
because only the checkpoint stage was inserted (`design/DV-TWOTX-20261021.md`).
The contract you are proving toward is `design/SECURITY-CONTRACT-20261021.md`:
100-bit per attempt, no grinding credit.

## Dependencies of the lead's cones on yours (23:35)

- **S7** needs the source `four_dots`, opening, fold and geometry joins from
  S4/S5 to finish its whole-function certificate.
- **S8** needs the source EbyKDot and relation-finisher laws, from the S3/S9
  EbyK work.
- **Every** lead cone (multiproof, checkpoint, S7, S8) also waits on S2's caller
  binding.
When these land, the lead composes them; please state their joins against
`dV_frozen2`, in total form where possible.

## After your S4 adoption (lead, 2026-10-22 12:20)

The lead re-pinned its cones to your adopted source (C3-BIN addenda 11:50,
12:05, 12:15; `evidence/lead-repin-20261022/REPIN.md`,
`evidence/s10-repin-20261022/`). S7/S8 declarations, parser, multiproof and
checkpoint items are unchanged. The adopted ELFs reproduce
(`40dc7574…`/`12cb0bc2…`/`121f3e29…`) and all 140 S10 ordering relations
survive. One item needs you: `canonical::Q::from_limbs` changed body
(`be073dde…` → `5c935940…`). It is reached by `EbyKDot::push` via `checked_q`,
so the S5 four-limb predicate/Option correspondence must be rebound (S5 is
yours; the S8 consumer is the lead's). Please state it against the new body.

## S2 lead caller interface (worker, 2026-10-22)

Additive interface: `lean/S2LeadInterface.lean`; exact consumers and statement
cross-check: `design/S2-LEAD-INTERFACE-20261022.md`; receipts and semantic field
audit: `evidence/s2-interface-20261022/`. No A candidate/evidence was edited.

Please export fixed-input witnesses for `S2CallerFacts`: `proofBytes`,
`publicBytes`, `proofSuffix`, `proofLength`, `checkpointBytes`,
`checkpointLength`, `nodeViews` (all b<2,k<3), `y1Input`, `observerNone`,
`reachedPrefix`, `callOrder`, `accountFrame`, `writtenMetadata`, `oracle`.
Proof/public snapshots must identify the externally fixed stored proof and
`tr.statement.pubBytes` at reached calls. Checkpoint save/TX2/resume must use
the same verifier-checkpoint bytes, with the actual writer→account→reader
transport proved separately. The record contains no observation/log/verifier-
output equality; see `FIELD-AUDIT.md` for every field's meaning.

Read-only inspection of your s126 worktree found the qualification now lists
**15/15** windows plus public/checkpoint roots. The important gap is the domain:
actual SDK native framing covers the bounded **decoder-error prefix**, whereas
the lead needs successful caller execution and fixed byte identities. Your
`all_buffers_frame` correctly leaves common-execution source-certificate
instantiation external. Its 58295-byte account frame must become the actual
[688,58295) suffix (57607 bytes); `proof_suffix_bytes` checks that conversion.
`LinkedFirst`/`stage1_current_call` expose existential owned buffers, not yet
the fixed external stored/public snapshots. `observer_none` and `first_success`
are useful exact owned Option/current-tx1 links. TX2 reconstructed ASF8 public
bytes, verifier checkpoint retention, runtime/source transport and account
metadata effects still require witnesses; ASQ8 bytes and the Pool checkpoint
are different carriers.

Checked composition also caught distinct extracted checkpoint/multiproof
`Digest32` types; `multiproofDigest` transports the identical implementation
fields. The total per-call multiproof oracle law implies the weaker checkpoint
success law via `checkpoint_oracle`; byte preservation proves neither law.
`compose` derives checkpoint bindings, six slot premises, S7 initial Progress
and actual S8 CallerInvariant from the independent lead S7 PushTrace. General
resumed Progress, saved-ten-state provenance and field meaning stay with the
lead cones; these are not disguised as S2 facts. No whole S2 or AcceptedRunJoin
closure is claimed.

Focused local compile passed (attempt6): exit0, 28.946s, peak RSS3.65GB,
swaps0; all six theorem audits standard-only. No further Lean compile is
needed for this handoff. No shipped source/ELF change or push.

## Import-union adapter adoption (release gate 1, 2026-10-22)

The real adapter is now `lean/ImportUnionNamedDiscriminant.lean`. It delegates
reader and instance generation to the pinned Aeneas generator, then gives the
instance the name `<fully-qualified-enum>.instDiscriminant`. It preserves the
scalar, explicit tags (including `u8 [1,2]`), and generic binders. The pinned
Aeneas library itself is unchanged. Rebuild this adapter if that library changes.

The deterministic migration tool is `tools/import-union/migrate.py` at repository
root. This worker applied its default scope only (`docs/research/**/lean/`),
including generated standalone type-bearing modules. No `lean-candidates` file
was edited. Session A should apply the **same script** to its chosen adopted
candidate roots, each explicitly listed, for example:

```sh
python3 tools/import-union/migrate.py --apply \
  --candidate-root docs/research/100bit-spend-path-20261013/lean-candidates/s3-s9-current-repin-20261020 \
  --manifest /tmp/session-a-import-union-before-after.json
python3 tools/import-union/migrate.py --check \
  --candidate-root docs/research/100bit-spend-path-20261013/lean-candidates/s3-s9-current-repin-20261020 \
  --manifest /tmp/session-a-import-union-check.json
```

Repeat `--candidate-root` for each adopted extraction. The script changes only
`@[discriminant ...]` to `@[import_union_discriminant ...]` and adds one
`import ImportUnionNamedDiscriminant`; all other bytes remain unchanged. Keep
the before/after manifest from the **first** apply; a second apply is a no-op
and produces an empty manifest. Commit the manifests with the adopted pins.
Do not migrate alternative source variants into the same environment as if
they were separate modules: one selected provider owns each Lean module name.

Compile the adapter first, then changed Types roots, then all transitive
consumers in the selected S10 manifest bottom-up using a private object overlay.
Include both `AspisR1TerminalDecoder.Types` and `AspisR1WithdrawalCaller.Types`:
their old `instDiscriminantPoolV1TransitionKindU8` collision stopped part 52 at
`ExtractedDecoderCallerBridge`. Re-pin source and object hashes and audit raw
`ModuleData.constants` across the final union, since environment enumeration
alone suppresses accepted duplicate equation theorems. Duplicate definitions
are errors; duplicate generated equation theorems with the same type are allowed.
Use the existing host caps (6G high, 8G max, zero swap), retain the cache, and
record all AGENTS formal-release fields. Keep this import-compatibility result
separate from discharge of soundness or privacy premises.

Worker receipts: `evidence/import-union-20261022/`; migration hashes are in
`migration.json`, exact-byte validation in `migration-validation.json`, and
focused adapter checks in `adapter-host/`. The final union source is
`lean/ImportUnionReleaseGate.lean`. This handoff requests Session A's candidate
adoption and S10 re-pinning; the worker does not claim those edits are done.

The full gate also exposed stale-provider collisions beyond discriminant
attributes. Use the canonical `AspisR1PublicSerializer.Types` from
`lean/bridge-verify-prefix-fe80-20261017/` (already named readers); an older host
object still generated anonymous Error instances. `R1D18Transport` and
`R1PoseidonMap` are now compatibility imports of their single canonical model
owners. The current `R1SpendRelation` already imports `SpendRelation`; do not
reuse the older full cached model: its Rspend/check omit AppendBinding.
`tools/import-union/repin-model-aliases.py` records the canonical source choices
and forces their entire retained consumer closure. In particular use the
append-aware R1SpendRelationExtraction source pinned in model-alias-repin.json.
These provider changes require consumer replay, even when a module's own source
bytes are unchanged.

Raw census must read `.olean`, `.olean.server`, and `.olean.private` together.
Exported theorem stubs in the public part alone can look like axioms.
`tools/import-union/RawUnionScan.lean` streams the complete module metadata and
compares duplicate types as expressions, without expanding shared expression
DAGs into text. Keep compatible same-type theorem overlaps in the report;
instances, definitions, and incompatible types remain blockers. A successful
import does not replace this census.

Re-enumerate the **final** object graph after changing providers. Canonical
imports can expose retained consumers absent from the starting cache graph.
`tools/import-union/complete-rebuild-closure.py` checks the final graph against
the source rebuild plan and prepares missing consumers plus their reverse
closure; it refuses an unchanged closure replay with no missing consumers.

The complete raw census includes upstream libraries. Run enumeration with
`RawUnionScan.lean`, then `prepare-raw-batches.py`, the generated capped Lean
batch targets, and `merge-raw-batches.py`. Each type-comparison job checks at
most 100 names as exact expressions. Reading all 8,164 modules twice in one
interpreter exceeded the 7GB guard; splitting enumeration/comparison fixed it.
Metadata tools read object files at runtime: bind their rebuild epoch to the
provider/closure snapshot when adopting a new candidate, rather than reusing
metadata solely because the `Lean` import is unchanged.

The two unchanged `SamplerWordRead.unwrap_success` / `read_success` helper
audits mention the existing opaque `core.fmt.Formatter` type. Preserve this
exception inventory; they are not standard-only audits. The requested combined
release audits and new theorem audits are standard-only. This import gate does
not discharge any soundness, privacy, decoder, or efficiency premise.

Final worker result: 851 targets accepted; all 807 affected roots/consumers
rebuilt. Aggregate IU-1328 exited 0 (1.753723s, peak
4,587,852 KiB, swap 0), with 77 standard-only release audits.
Full census: 8,164 modules / 566,510 declarations, zero duplicate definitions
or instances; all 614 theorem-name overlaps have exactly identical types.
See evidence/import-union-20261022/summary.json for source revisions, resource
fields, the two unchanged Formatter helper-audit exceptions, and full receipts.
Candidate adoption remains Session A's work; no lean-candidates source was edited.

When adopting S3, update the aggregate diagnostic check of the old anonymous
`instDiscriminantErrorIsize` to the new qualified S3 instance name (or use
`#synth Aeneas.Std.Discriminant AspisR1S3InactiveSource.r0.Error Aeneas.Std.Isize`).
That old-name check intentionally describes the retained, untouched candidate.

## S2-I request — 2026-10-23: full forest public and composed first child

S2-I has NOT proved these session-A-owned children. The exact requested
statement types are `AspisR1.S2I.SessionAStatements.FullForestPublicPort`,
`FullForestPublicShape`, `ComposedFirstPort`, `ComposedFirstValue` in
`lean/S2I_SessionAStatements.lean`. These are goal definitions, not assumptions
adopted by S2 or proved implementation instances. Their complete signatures
use the existing S2E full Statement, Vec, ProgramError and Result carriers:

```lean
PublicEval S := S → Statement →
  Result ((core.result.Result (alloc.vec.Vec U8) PE) × S)
FirstEval S := S → Statement → Slice U8 → Slice U8 → Usize →
  Result ((core.result.Result (alloc.vec.Vec U8) PE) × S)

FullForestPublicPort native children :=
  ∀ state statement,
    native state statement = children.«public» state statement
FullForestPublicShape native :=
  ∀ state statement bytes after,
    native state statement = ok (.Ok bytes,after) →
    bytes.val.length = 1880 ∧
      bytes.val.take 4 = [65#u8,83#u8,70#u8,56#u8]
ComposedFirstPort native children :=
  ∀ state statement publicInput proof split,
    native state statement publicInput proof split =
      children.first state statement publicInput proof split
ComposedFirstValue native ops vops :=
  ∀ state statement publicInput proof split cp after,
    native state statement publicInput proof split = ok (.Ok cp,after) →
    S2G.first ops vops statement publicInput proof split = ok (.Ok cp)
```

Required deliverable: CONCRETE definitions and proofs inhabiting these types,
not universally quantified arbitrary encoder/verifier callbacks. `native` must
be the actual source evaluator and `children` its installed S2E child. S must
be the native/owned admitted cut carrier, with original external byte snapshots,
Box/Vec owners, allocator and ordered runtime/oracle effects. If S is a subtype,
its admission predicate must contain only independently derived runtime/cut
invariants, never child success, output equality or a forest serialization fact.
The native↔owned relation is S2-H's interface; an inert ghost is insufficient.
An explicit relation for external execution traces must additionally retain
query prefixes on outer fail/div/abort, since Result itself returns no state
in those cases. The equations above preserve inner Err states but do not
manufacture an abort trace.

For `full_forest_public_port`, provide the full native
`encode_pool_v1_pair_forest_terminal_statement_v1` serializer, both private
transfer and withdrawal, all common/live-snapshot/frontier/payment fields,
complete ASF8 Vec1880 bytes, original format-error mapping to
InvalidInstructionData, allocation/abort and argument/account frame. The
concrete reference encoder definition must identify every byte, including
reserved/header fields; width/magic alone is insufficient. Payment216
`encoder_eq` and `RepinS6First.reuse_decoded` do not establish this theorem.

For `first_decoded_port`, instantiate the actual adopted candidate.tx1,
SolanaDigest and release observer None. Bind semantic_public to the SAME full
statement, original public1880 and proof57607 slices, instruction split10/11,
parser/node views, S1 prepared/challenge provenance, S3 coefficients, S4 dots,
S5 finish and S9 side updates. Include batch0, ten reached query callbacks,
checkpoint writer, exact returned Vec/capacity/ownership and all ordered digest,
error-log and allocation events. Rejected prefixes and error mapping must agree;
an accepted batch equality or an independently successful checkpoint is not
an instance. Do not assert callee-wide length1768 without a separate proof:
S2's existing first value theorem obtains that length at the later caller gate.

No source adoption, stronger cryptographic assumption, reduced metric or
new SDK trust field is requested. These goals remain open after this handoff.

## Your rows in the soundness port table (lead, 2026-10-23 19:15)

S2 is proved to its boundary (`S2W_D189Consolidation.accepted_run`). The verifier stage entries
`tx1`, `tx2_common` and `tx2_authenticated` are extracted with cone bodies opaque
(`design/VERIFIER-TOP-20261023.md`). Soundness now needs one accepted-run port per opaque body.
These rows are yours. Please state each as the port at its call site (the returned state
and ordered reads equal the corresponding `dV_frozen2` stage), against the CURRENT source (owned
adapter plus H5; release pins default `f8c0ec72…`, devnet `63ad3e9c…`):
- `prepare` / op7 (TX1, including the returned gamma scratch): bind the returned Prepared,
  scratch, transcript driver reads, parser and queries
  (`AspisR1ClaimPreparedBridge.InstalledMeaning.prepared_installed_meaning` is the nearest).
- `powers` / op17 (TX2): the resumed gamma, full array and no-read interpretation
  (`AspisR1LoopPowers.early_powers_total_exact`).
- The nested S3/S4/S5/S9 backends used by query/finish (grouped-pair, dot, strict codec, reducer,
  factored identities): complete parent-body instances with reached operand bounds.
- S6 first-decoded/semantic/public input transport, plus `FullForestAcceptedRoundtrip` (the
  1,880-byte public encoding round trip).

## Critical path now runs through your `prepare` row (lead, 2026-10-24 09:20)

Overnight port jobs closed or nearly closed the lead rows. Proved: flush and finish (accepted
finish equals Frozen2 on the same returned 12-step state); batch accepted-only transport for both
transactions; geometry, pending and query observations; checkpoint writer/reader cuts. Two lead
rows (checkpoint writer provenance and batch) are now blocked only on **your** `prepare`/op7
port. A proved counterexample shows that leaving the preparation child unbound allows a wrong
header tag, so writer provenance cannot be derived without it. Concretely we need
an S1 `PreparedBinding` on the actual prepare/resume returns: the returned Prepared, gamma scratch,
transcript-driver reads, parser rows and queries equal the model's. That, plus `powers`/op17 and the
S3/S4/S5/S9 primitive instances, are the remaining session A inputs to the soundness composition.


## Lead integration checkpoint (2026-10-24 11:05 UK)

Q1/Q2 are merged and pushed through 6394df2389. Session A files were not changed.
The query consumer is now `Port5Q1_Complete.accepted`; its local preparation
interface `Port5Q1_QueryPorts.SessionAPrepare` binds the SAME returned raw queries,
rho/canonicality and alpha1 to the parsed SourceInputs. Primitive interfaces are
`SessionAPrimitives`, `Port5Q1_GeometryCanonical.SessionAPrimitives` and
`Port5Q1_Domain.SessionADomain`. Please check their complete quantifiers when
instantiating them: if a primitive law holds only on reached/canonical operands,
report the precise required guard rather than assuming a global law.

The lead is composing native op18 and same checkpoint state (Port6CK), and
indexed authentication plus sufficient security transport (Port6AUTH). Q1's
collision-free recovery premise cannot itself establish the current all-oracle
AcceptedVerifierJoin. This is under explicit review, with no target change or
new all-oracle claim. Your prepare/op7, powers/op17, primitive instances and
S6/S10 obligations remain as in the previous handoff. No duplicate work on your
live candidates is assigned.


## Build-host solver ownership review (2026-10-24 11:16 UK)

A read-only resource check found z3 PID 2095724, PPID 1, elapsed 1-08:12:58,
CPU time 1-08:11:49, RSS 4,769,532 KiB, state R. Its cwd is
`/home/dombarker/project-offloads/s126-real-sdk-20261021/aspis-s1-claim-uf-v2`,
executable `s126-real-sdk-20261021/z3-tool-v1/bin/z3`, and cgroup is
`run-r398b48eab4d44c4295b8e78a9cd95da9.scope` under user@1000.service/app.slice.
That scope contains only z3, MemoryMax=8 GiB, MemorySwapMax=0. This appears
detached from its original controller; the lead has not inferred its proof
status or terminated it. Please review this owned solver and its original
receipt against the ten-minute progress rule, preserving any failure evidence.

The host had 40 GiB of populated capped-scope reservations, including background
services and one current Lean scope, below the 55 GiB safe reservation ceiling.
This solver prevents a quiet-host absolute prover timing gate. No processes,
files or source candidates belonging to session A were changed.


## Lead source-interface integration (2026-10-24 11:37 UK)

Port6AUTH is reviewed/merged/pushed through b50ab72e92. The exact source query
consumer is now Port6AUTH_Query.accepted: actual native batch returns feed
indexed recovery on the literal first source annotation record, then Q1's
saved-ten/continued-twelve accumulator conclusion. The compiler maps and both
passes' word stability are derived. Existing prepare/root, primitive, domain
and P6 boundaries remain explicit, with the same local ownership.

Port6AUTH_Headline.final_soundness is an additive sufficient interface for the
unchanged contract. It does not establish all-H AcceptedRunJoin. Its open
CleanAcceptedModel requires actual terminal Checks and classifier no-hit;
charged-prefix containment, source call cap1161 and runtime carrier instance
also remain open. Collision is charged once and the exact full bound is
preserved. Port7CLEAN now owns concrete driver terminal/no-hit composition and
requisite source trace embeddings; Port6CK still owns native op18/checkpoint
state. Neither worker duplicates your prepare/powers/primitive/S6/S10 rows.
See evidence/port6auth-20261024/STAGE3.md for full before/after and retained
premises. Both deployed targets remain not yet established.


## Lead checkpoint closure at local boundary (2026-10-24)

Port6CK_Complete.accepted now derives saved-to-resumed state equality from one
actual TX1 and current op18 on its exact saved Vec, then advances its returned
state through twelve actual calls. Port6CK_Ordered.accepted preserves the six
ordered digest observations. SourceJoin.source/provenance are ready for
VTop_Checkpoint.reader_join/writer_join. Your preparation/primitive/powers and
runtime/artifact obligations remain explicit; no deployed closure is claimed.
Port7CLEAN owns the enclosing driver composition; no duplicate session A work
is assigned. Full assumptions and receipt review are in the latest C3-BIN
addendum and evidence/port6ck-20261024/HANDOFF.md.


## Concrete effectful prepare interface needed (2026-10-24)

Port7CLEAN derives terminal Checks from actual local calls, but its compiled
TraceObstruction.no_sampler_embedding shows that native return-value laws alone
cannot supply source sampler containment: valueOnly returns invoke ops call
exactly while its driver log is empty. This is not a frozen-driver or security
counterexample. The missing item is the pinned effectful body Implementation.

Please include in your owned prepare/op7 deliverable the actual effect program
and its source correspondence, with the SAME returned Prepared/gamma state,
ordered sampler frames/read history and early-rejection behavior. Successful
return equality/PreparedBinding alone is insufficient for adaptive security
transport. The exact consumer is Port7CLEAN_Accepted's first-source sampler
containment and Port6AUTH_Prefix charged-prefix replay; see Port7CLEAN STAGE2.
Accepted-only local refinement may suffice, but the enclosing probability/count
argument must justify its use and retain rejected effects. Do not assume
all-driver equality to manufacture this local instance.

Lead Port8EFF owns effectful op5 batch and checkpoint8/18 composition, concrete
VTop installation and reached-call/log embeddings, reusing the newly merged
Port6CK. It retains your op7/op17 and primitive boundary explicitly, without
duplicating your source work. No protocol/trust/security change is authorized.


## Build-host solver observation (2026-10-24 12:03 BST)

Read-only /proc and cgroup checks now show PID2095724 and its exact
run-r398b48eab4d44c4295b8e78a9cd95da9.scope absent. The lead did not terminate
it. No outcome is inferred: obtain its owner's receipt to establish success,
failure or cancellation. This removes the previously observed solver load,
but does not itself establish a quiet timing interval. A focused Lean process
was live during the check. Recheck all host activity/reservations immediately
before any later absolute prover timing gate; no timing result is claimed.


## Oracle-response interface qualification (2026-10-24)

Port8EFF checkpoint effects are merged as CONDITIONAL trace evidence. Lead found
CheckpointCode.program obtains fixed D.digest then `.ask ... (fun _ => ...)`,
discarding H's reply. Its Oracle D hash H assumption explains the local trace
theorem, but this does not yet supply a fixed adaptive source probability
experiment. Port9OR now owns the reply-driven checkpoint repair and subsequent
physical op5 lift under the remaining64/100 Lean allocation.

Your effectful prepare7 producer likewise needs actual oracle replies to drive
transcript continuations; native value equations plus recorded asks are not
sufficient by themselves. Separate per-H native interpretation from a fixed
Program sampled under the oracle law; do not assume all-H agreement with one
fixed native digest or condition the oracle. Existing source/trust/ownership
boundaries remain; no protocol/security change is proposed. Prepare sampler
history and rejected prefixes remain your local source deliverable.


## Reply-driven source effects ready (2026-10-24)

Port9OR now merged: Code.correspondence separates fixed response-driven Program from per-H native interpretation; actual reader branches consume replies. Installed.effects covers physical batch op5 (duplicate hashing before compare, rejection suffixes and scratch), plus8/18. FirstBatch.first_batch supplies accepted-source batch1 chronology. See evidence/port9oracle-20261024/README.md/STAGE1-3. Your prepare7/powers17/primitive frontier is unchanged. Lead next owns physical-to-canonical batch read containment for Port6AUTH contains; no duplicate sampler work. Full-source accepted-failure domination, source1161 and StoredCarrierBinding remain open. Both targets not yet established.


## Both physical batch authentication traces ready (2026-10-24)

Port10AUTH now reviewed/merged. Installed.accepted proves complete accepted physical op5 observation equals canonical sourceBatch log; FirstBoth.accepted embeds both batches in the same first accepted source record. Retains exact wire/query/root/node-view provenance at actual Prepared witnesses, existing ParentGate/LeafGate and P6 lowering. Lead next owns instantiating those provenance equations and feeding Port6AUTH, without duplicating your prepare7/sampler/powers17/primitive work. Full-source domination/no-hit, source1161, StoredCarrierBinding and release identity remain open. See evidence/port10auth-20261024/README.md/STAGE3. Both deployed targets not yet established.


## Exact parser/prepare producer needed after provenance integration (2026-10-24)

Port11PROV now derives current18 raw queries and two stored roots from actual TX1 p0 through SAME saved Vec, plus actual folded roots/fixed node views. Authenticated.accepted composes both batch traces with Port6AUTH recovery. Exact open source call is eval H(rest(.op7 D semantic proof hash none(Array.repeat29zero)))=ok(.Ok p0,g0), with actual op3/op4 returns now exposed by FirstBoth. Please supply reviewed committed parser/prepare7 provenance at that call: canonical parse validity, sampled q/transcript association, copied stored roots and complete effects/counts. Use these checkpoint preservation results instead of independent resumed BodyMatches witnesses. Existing powers/query/finish primitive and sampler frame/no-hit requirements remain. P6 total oracle field is still explicit in final auth boundary. Lead next owns physical batch count potentials under remaining35 attempts. Both targets not yet established. See evidence/port11prov-20261024/GATES.md for exact interfaces.


## Extraction/resource findings requiring scoped assessment (2026-10-24)

Privacy isolated candidate005 validation found realDrop probe Guard(counter+=1) emitted as unchangedcounter while overall translation failed in destructor. Candidate007 now rejects structuredDrop/escapingrefs beforeoutput and is unadopted. This is not yet a baseline installedbinary regression: next worker will run no-refinederror minimalbaselineprobe beforegeneralizing. Retain existing source proof boundaries; do not promote partialoutput from failedtranslation. Exact source/output in provercandidate RNG-EXTRACTOR-CONTINUATION. No A tool/source was changed.

Reused reservation scan covered user app.slice only and omitted Docker/system scopes; historical fullaggregate<55GiB evidence for affected privacyjobs is missing, although individual caps/swap are recorded. Lead currentall-scope finitepopulatedsum24.375GiB includesDocker/services; notretroactiveevidence. Newprivacylaunchers must inventory hierarchy/systemDocker beforeheavyjobs. Please assess your launchers for the same issue; lead will not change your activejobs or sharedtools.


## Resource-accounting correction (lead, 2026-10-24)

Read-only inspection of Port9OR_compile/Port10AUTH_compile/Port11PROV_compile confirms their admission scan is rooted in user-1000's user@1000.service and checks direct cgroup.procs in *.scope. It omits system.slice Docker/services and hierarchical populated descendants. Earlier lead statements that their static aggregate checks passed mean only the recorded SUBSET arithmetic; claims of complete historical aggregate<55GiB are superseded as unverified. Individual no-swap/MemoryHigh/MemoryMax/TasksMax and source/axiom evidence are unaffected. A new current host-wide finite capped subtree inventory found24.375GiB; this cannot reconstruct historical totals. Future admissions must include all populated capped subtrees once and retain unreadable/uncapped-background handling. Existing proofs are local mathematical evidence, not retroactively compliant resource/release certificates. D199 has the privacy finding and correction path.


## Owned physical read counts ready (2026-10-24)

Port12COUNT now reviewed/merged: installed op5 batch0<=477,batch1<=563 on all input/H/outcomes, writer/current18<=3each; owned subtotal<=1046 with repeated hashes and error prefixes. These are actual physical Programs, not inherited modelcounts. Full1161 still needs your concrete effectful rest producer's executed subtotal<=115 and actual driver partition/composition. Exact parser/prepare7 provenance request above remains. Lead next uses6conservative slots to remove unnecessary native-D totaloracle premise from indexed authentication by a proof-only totaldictionary; no sourceexperiment change or sampler duplication. Historical complete aggregate accounting remains unverified for inheritedlaunchers as corrected above. Both targets notyetestablished.


## Addendum (lead, 2026-10-24): indexed authentication without native totality

Reviewed Port13GATE c0796e88f5 and merged as 8f19bb29d5. Port13GATE_Authenticated.accepted preserves the complete Port11 sourceAccepted premise and subsequent witnesses/conclusion; native-D full P6Boundary and redundant binary callback are removed. A proof-only Unit dictionary constructs canonical comparison totality without replacing the fixed response-driven source Program. Actual native successes and original ordered logs still pass through Port10AUTH_Installed. Occupied/sibling ParentGate and LeafGate, strict parse/query/root association, Std/unwrap, frame/cap/no-hit, concrete delegated rest and source1161, StoredCarrierBinding and release identities remain open. No new probability conditioning, collision term or trust assumption. Both deployed targets not yet established.

Lead independently read helper/consumer/full before-after signatures, checked exact unchanged conclusion, generator --check, all three final source hashes, seven standard-axiom audit reports and caps/swap receipts. Audit005 at0a7aab30af plus exact source/dependency hashes: exit0,1.997596704022726s,peakRSS4463268KiB,swap0. Cached dependencies reused with source/object assessment; no coherent release replay or new ELF gate. Complete host-wide admission scanner and nested/system-Docker/uncapped/missing-data fixtures reviewed and passed; five fresh locked admissions each24.375GiB+8GiB<55GiB. This does not repair historical aggregate evidence.

Budget remains218 actual compiles+1pre-Lean charge=219/220 charged,1slot remaining; Kani0/20. Next scoped worker will inspect and instantiate actual local callback producers/adoption where genuinely sufficient, with a committed dependency assessment before proof work, without duplicating session A prepare/powers/sampler.


## D200 — Native Drop probes retained; complete output still fails (lead, 2026-10-24)

Reviewed unmerged provercandidate80a4a07181/aeec7331d8, native-entropy REPORT/design. Optimized five Guard probes give0->1; pinned baseline translations020/022 exit0 yet emit identity real_drop. Whole020 emission fails Lean11560 on borrowed Option.take return shape;022 remains uncompiled, swap signature mismatch observed. No kernel-accepted baseline counterexample or general installed-backend unsoundness claim. Candidate007 actually rejects minimal and selected64 beforeoutput. No native refinement/E1/source premise discharged. Candidate stays unmerged; no shipped/installed tool change or new trust.

Lead read actual probe/output/diagnostics/interpreter Drop branch and complete structural/audit sources; independent read-only collector/source association,187integrityhashes,11scanner+3Dockerbarrierfixtures passed. All12extractions+4Lean receipts retain exacthashes/commands/caps/swap; audit11562 ataeec7331d8+native-entropy-drop-probe exit0,1.03s,RSS2621948KiB,swap0,three no-axiom structural/library reports. This is interface inspection only, not source theorem. Lead found generated heartbeat/recursion defaults in new structural Types; nextworker must remove them and recompile changedTypes/dependentaudit, preserving oldhashes as historical. No claim of whole-source closure. Historical completeaggregate remains unverified; current hierarchicalscanner/barriers reviewed.

Budget backend7/12,Lean223/260,Kani44/60. Lead allocates12newextracts after24/24 exhaustion, ceiling36. Nextnative-drop worker designs and attempts realdrop_glue/loan handling, complete kernel-accepted Guard regression then actualZeroizing; no owned-wrapper substitute over unresolvedcleanup, noinstalledtooladoption. Both deployedtargets notyetestablished.


## Addendum (lead, 2026-10-24): callback audit; actual driver partition next

Port14LOCAL d297222029 reviewed: callbacks are proof-only comparison witnesses; native parent/leaf accepted physical transport already exists in Port9/10. No callback wrapper or kernel theorem added and no source assumption discharged. Source audit43files/10byte-identicalhistoricalgreenreceipts plus localadmissionfixtures independently rechecked read-only. Full source interfaces and unchanged endpoint statement retained. The all-failD counterexample explains why literal totalParentGate cannot describe failure-preserving nativeproducer; choosing canonicalcomparison witnesses is not nativeadoption. No shipped/security/trust/keychange or formalreplay.

NEXT-PRODUCER.md identifies exact actual TX1/TX2 sites and weighted delegated bound:2*w3+w4+2*w6+w7+2*w9+2*w10+2*w11+w12+w17+w19<=115. Unrestrictedrest can issue1162asks at firstop3 and reject, so full1161 is false without localproducerbounds. Lead next owns proving actualdrivercontrolpartition/all-outcome composition from explicit per-op budget producers, using realreturned savedVec/Prepared and 477+3+3+563=1046, NOT checkpointChainprojection equality. SessionA retains concrete parser/prepare/powers/sampler/primitive bounds; no duplicate work. A conditional partition theorem will close only sourcecontrolcomposition, not concrete115orfullrelease. Budget219/240charged,21remain,Kani0/20; no newLean allocation.

Client64 worker2349 now implements D162 caller migration separately on unmergedcandidate, tools/scripts only with offline mocks; no chain/key operations, crates/programs changes or nativeprivacy/adoptionclaim. NativeDrop386 remainsactive. Bothdeployedtargetsnotyetestablished.
