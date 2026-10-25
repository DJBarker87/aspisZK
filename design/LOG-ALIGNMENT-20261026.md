# Oracle log alignment: architecture decision scope

S2 OPEN; **target not yet established**. This is decision support, not a
transport theorem or source/model refinement. No security contract, trust
item, shipped byte, artifact pin or other worker module changes here.

## Finding and recommendation

Choose **B: a source-faithful frozen3**, but scope the change correctly:
retain frozen2's existing sampler prefix and batch order, and give checkpointing
its own physical public-byte carrier. Do not redesign Fiat–Shamir merely to
repair the terminal-decision interface.

RawK's checked obstruction is accurate for its quantified target:
`GExq_CallerRecord.program` versus **bare** `OraclePortFrozen2.dV_frozen2`.
The first starts with byte85 and the second with byte16 (or has no queries).
It does **not** prove a first-position obstruction against the headline's
complete `OraclePortStoredExperimentC4.verifier D dV_frozen2`.
That verifier runs all 33 sampler rows before calling the decision.
`LogA_Dependencies.verifier_initial_head` checks its semantic initialization
head, on an initial-row constructor, without acceptance. This corrects the
scope of the inference, not RawK's theorem.

There is nevertheless a concrete checkpoint-carrier mismatch. The source
hashes the original ASF8 public statement (1880 bytes); the model hashes
`tr.statement.pubBytes`, the section-9 semantic encoding (1455 bytes for
private transfer, 1427 for withdrawal). The semantic serializer explicitly
omits pool/domain/sequence and source-current-root fields. See
`programs/r1-cost-probe/src/lib.rs:first_decoded`,
`r1_pool_adapter_owned.rs:stage1_owned`, `verifier.rs:checkpoint/resume`,
`pair_forest_semantic_terminal.rs:r0::Public.public_bytes`, and
`pair_forest_terminal.rs:POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES`.
`LogA_PublicBytes.physical_ne_semantic` checks address inequality from physical
width1880 and the **actual** `SemanticPublicWire.parsePublic` premise.
It does not derive those premises from native acceptance.
Distinct addresses can have equal oracle answers: no hash inequality follows.

## Notation and evidence boundaries

Indices below are zero-based, issued calls, retaining duplicate reads.
`H` is the same byte-address oracle. `S` is the exact stored proof suffix
(57607 bytes), `P` the physical ASF8 bytes, `U=semanticPublic(statement)` the
section-9 bytes, and `C` the saved checkpoint (1768 bytes), with body
`C[0:1736]`. TX2 uses the same S/P/C only after the retained caller/history
bindings; that equality is not furnished by this scoping job.

The inventory is derived from installed source definitions and source inspection,
not a new universal accepted-run log theorem or a concrete trace measurement.
`RawK_TraceLogs.ordered` concatenates actual returning children chronologically;
`RawJ_RecordCuts.native` selects their same native accepted pair;
`RawJ_OriginalAccepted.accepted` associates that containing log with H under
its named boundaries. `SdkD_PrepareSource.code/source_run`,
`GExq_FirstCode.code`, `GExq_SecondCode.common`, `SdkD_FirstOrder.accepted`,
`SdkD_WriterSource`, `SdkD_ReaderRoots/Queries` and
`SdkD_CheckpointBinding.fields` identify the preparation, batch/save and
resume carriers. RawJ's 1018/903/1921 bounds are conservative bounds, **not**
exact call counts. They do not certify complete frozen2 correspondence.

## Complete source schedule on an accepted pair

Set `A_r` to the absorbed digest and `T_r` to the incoming 32-byte state.
`le32` is four little-endian length bytes; concatenations are flattened
`Digest32::digest`/hashv parts, not extra hashing operations.

| Source indices | Operation and exact input | Issued count |
|---|---|---:|
| 0 | `UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3 || 00 || le32(len U) || U || c1root` | 1 |
| `1+3r,2+3r,3+3r`, r=0..26 | absorb `T_r || 00 || (a0+r) || record_r`; squeeze `A_r || 01`; advance `A_r || 02` | 81 |
| 82 | opening reseed `UNPROVED:R1:PRIVATE-SALTED:P3 || 02 || T_27` | 1 |
| `83+3(r-27)` through `85+3(r-27)`, r=27..30 | absorb `T_r || 00 || (a0+r) || le32(len payload_r) || payload_r`; squeeze; advance | 12 |
| 95 | query-row absorb, row31: `T_31 || 00 || bf || le32(2048) || final_message` | 1 |
| `96+2j,97+2j`, j=0..7 | squeeze `V_j || 01`; advance `V_j || 02`; `V_0=H(input95)`, `V_(j+1)=H(V_j||02)` | 16 |
| 112,113,114 | rho row32: `T_32 || 00 || c0 || le32(0)`, then absorbed-state `||01`, `||02` | 3 |
| 115 onward | batch0: kinds0,1,2, each leaves then parents, as specified below | `L0=30+N0` |
| `115+L0` | checkpoint writer `S` (raw, no added tag) | 1 |
| `116+L0` | checkpoint writer `P` (raw1880, no added tag) | 1 |
| `117+L0` | `UNPROVED:R1:checkpoint || C[0:1736]` | 1 |
| `118+L0,119+L0,120+L0` | TX2 resume: `S`, `P`, same domain/body checksum address | 3 |
| `121+L0` onward | batch1: kinds0,1,2, each leaves then parents | `L1=36+N1` |
| after batch1 | finish relation, final dot, settlement-facing return: no further verifier oracle calls | 0 |

Rows0..26 use **framed semantic records**, already containing a tag and
four-byte logical payload length: rows0,1,3..13 empty tag0; row2 tag1/C2root32;
row14 tag3/claim32; rows15..24 tag2/polynomial896 each; row25 tag4/claims3712;
row26 tag5/beforeZ1 values928. Row0's record is five zero bytes, not an omitted
absorb. Compact field expansion happens before hashing. Rows27..30 payloads
are respectively y1 expanded928, inactive32, round0 polynomial224, and
folded_root32 plus round1 polynomial224. `r1_wire.rs:begin`,
`r1_semantic.rs:verify_finish/semantic_rounds`, `verifier.rs:Prepared::new`,
`transcript.rs:new/block/queries/scalar_k` determine this order.

The query method **issues all eight pairs even when the scan succeeds earlier**.
`r0_transcript.rs:queries_from_pairs` selects the advance at the first successful
scan (or fails after eight); rho uses that selected state, not necessarily V8.
The unused later calls remain visible. The model does the same via
`QuerySampler.chain` plus `Q22.scanOut`. Do not substitute the separately
short-circuiting `Q22SamplerProgram.loopProgram` as its query schedule.

Each batch kind hashes every sorted opening, including duplicate indices:
10 leaves per kind in batch0, 12 in batch1. Keys sort `(index, source position)`;
kind0/1 use `q[pos]`, kind2 uses `q[pos]/4`. Each duplicate is compared immediately
by **digest**, not preimage bytes. Then padding/node-count guards run, followed
by18 parent levels, increasing parent index within each level. No postorder
executor or deferred duplicates are used. For a distinct index set I define

    N(b,k) = sum(h=1..18) | { floor(i / 2^h) : i in I(b,k) } |.
    N0 = N(0,0)+N(0,1)+N(0,2); N1 = N(1,0)+N(1,1)+N(1,2).

This parameterized formula is the exact count; accepted adversarial queries
need not have fixed distinctness. There is no universal constant parent count.
The opened leaves precede parents, including on collisions accepted by digest
duplicate checks. Parent inputs use computed children plus supplied sibling
words, in source order. Installed batch evidence is in
`SdkD_FirstPaths`, `SdkD_PairBatches`, `RawJ_BatchesAccepted`; the complete
source/model result is still open.

| Domain/shape | Total accepted source calls |
|---|---:|
| semantic initialization domain (38 bytes) | 1 |
| state-prefix + `00,label` absorption, labels a0..c0 | 33 |
| state-prefix + `01` squeeze | 40 |
| state-prefix + `02` advance | 40 |
| opening reseed domain (29 bytes), tag02 | 1 |
| leaf `10 71 || packed480 || salt32` | 22 |
| leaf `10 f1 || packed128 || salt32` | 22 |
| leaf `10 72 || packed128 || salt32` | 22 |
| parent `12 || left32 || right32` | N0+N1 |
| raw S / raw P | 2 / 2 |
| checkpoint domain (22 bytes) + body1736 | 2 |
| **Total** | **187+N0+N1** |

These counts cover the installed two-transaction verifier/caller oracle program,
not unrelated Pool instructions, external prover queries or transaction retries.

## Complete frozen2 sequences: three different levels

**Terminal decision** (`OraclePortFrozen2Decision`,
`RowOrder_FrozenSchedule.decision`): batch0 L0 calls; six checkpoint calls
`S,U,Dc||body,S,U,Dc||body`; batch1 L1 calls; pure finish. Total **72+N0+N1**.
It does not initialize or squeeze a transcript. Its batch indices are
0..L0-1; checkpoint indices L0..L0+5; batch1 starts L0+6.
At any admission/parse/query failure its log is empty; failed batch0 retains
its exact prefix; failed batch1 retains batch0 plus all six checkpoint reads
and its exact rejecting prefix. The table above describes accepted runs only.

**Complete verifier** (`OraclePortStoredExperimentC4.verifier` ->
`OracleDecisionFeasibilityCore.verifier/verifierFrom`): first the115-call
sampler, then that decision. The sampler's initialization uses U and the same
semantic domain; row26's post-advance opening reseed, all eight query pairs and
row32 rho match the source schedule at the byte-grammar level. Its count table
is the source table with raw P replaced by raw U, and a correspondingly changed
publicHash field/checksum address. Thus **187+N0+N1** calls, under aligned
submitted rows/roots/challenges/parsed bytes; this alignment remains to prove
on the installed source. Source physical P is not U.

**Headline annotated experiment** (`OraclePortStoredExperimentC4.recorded`,
`OraclePortStoredAdmissionC4.annotated`, `OraclePortFrozen2Consumer.projected`):
prover log, then a first complete verifier pass, then a second complete verifier
pass after enriching the literal proof with recovered words. `verifier_enrich`
preserves each query. Exact log is `log(P) ++ V ++ V`, not one verifier pass;
length is `len(log(P))+2*(187+N0+N1)` in the aligned accepted class. Memoization
reuses answers in the repeated pass; issued-call count and first-read count
are distinct. The current all-input formal bounds are verifier<=1161,
annotated length<=Q+2322, distinct reads<=Q+1161; batch0<=477,
batch1<=563. These are model bounds, not newly transferred source bounds.

## Exhaustive alignment table

`k` here indexes the **complete verifier's** calls. An M row means the same
logical address grammar with identity byte map, conditional on the same
source-derived public/rows/query/Prepared/accumulator witnesses. Except for the
small lemmas below, this is a source inspection classification, **not** an
inhabited `AcceptedRunJoin`. Against the bare terminal decision, every prefix
call0..114 is X (its domains are listed above), and subsequent M positions
are shifted by115. They are not extra calls against the complete verifier.

| Every source call family | Complete-model counterpart k | Class and byte map |
|---|---|---|
| semantic init0 | 0 | M: same semantic U/root/domain/length frame; standard U8/list conversion |
| semantic absorbs/squeezes/advances1..81 | same k | M: identity on flattened records and 32-byte states |
| opening init82 | 82 | M: same reseed domain/tag02/state |
| opening rounds27..30,83..94 | same k | M: identity; `framed(payload)=le32(len)||payload` is exactly what the source puts into separate hashv slices |
| query absorb95, pairs96..111 | same k | M: identity, including all unused scan-suffix pairs |
| rho112..114 | same k | M: identity using the selected query advance |
| batch0 leaves/parents | same k=115+j, j<L0 | M: same kinds, sorted positions/ties, immediate duplicate handling, level order and byte inputs |
| writer proof hash | 115+L0 | M: raw S, identity |
| writer public hash | none with same logical full-statement input | X: raw P1880 has no full-statement model counterpart. Model instead hashes raw U at116+L0 |
| writer checksum | 117+L0 | E: same body-authentication operation, publicHash field differs; map described below |
| resume proof hash | 118+L0 | M: raw S, identity, repeated read retained |
| resume public hash | none with same full-statement input | X: raw P1880; model-only raw U occurs at119+L0 |
| resume checksum | 120+L0 | E: same map as writer; source repeats its own saved address, model repeats its own |
| batch1 leaves/parents | same k=121+L0+j, j<L1 | M: conditional on the SAME resumed roots/query vector/data; not a consequence of equal query counts |
| finish | no call | pure computation in both; no oracle alignment row omitted |

If “public binding” is interpreted coarsely as the same logical operation,
the two X rows can instead be called **E with a noninjective projection**:

    P -> decodeASF8(P).semantic_public().public_bytes() = U.

That is not an admissible injective oracle-address rename. On the full carrier
it omits metadata; this job supplies neither an injectivity proof on admitted
statements nor a collision-preserving inverse. The two valid width classes are
disjoint, but raw queries have **no fixed domain tag**. Renaming all arbitrary
adversary addresses this way would merge oracle cells and change their law.
Model-only H(U) is also not the initialization H(domain||...||U||root).

The checksum encoding relation is explicit. Its input has length1758:
22-byte domain plus1736-byte body; within the body, bytes16..47 are H(S),
bytes48..79 are H(public). On the class where every other field agrees,

    Phi_H(a) = a.take(22+48) ++ bytes(H(U)) ++ a.drop(22+80),
    with source field a[22+48:22+80] = bytes(H(P)).

For **fixed H,P,U**, restricted to that fixed-field class, replacement has an
inverse replacing H(U) with H(P), hence is injective on the other fields and
keeps the checkpoint domain. It is NOT injective on unrestricted input bytes,
and is oracle-dependent: it requires H(U), which source did not ask standalone.
It is not a proved whole-world coupling or an E transport. If any other
Prepared/accumulator field has not been aligned, even this restricted map is
only conditional. `LogA_PublicBytes.changed_digest_changes_address` shows
that differing digest-field bytes change the flattened address, without
assuming distinct input addresses always have distinct hashes.

Hashv slice partition -> concatenation is injective only on the fixed slice
shape/width class. For arbitrary part lists it is not injective, e.g.
`[[a],[b]]` and `[[a,b]]` flatten alike. This is intentional because both source
and model oracle addresses are concatenated bytes. No cryptographic encoding
loss occurs merely from slice descriptors disappearing.

### Reorderings and adaptivity

There are **no source/complete-frozen2 chronological reorderings** in the
inspected aligned accepted schedule. The terminal-decision mismatch is a
missing prefix at that interface, not evidence that leaves can move before
transcript challenges. Specifically:

| Proposed movement or affected input | Does the input depend on answers crossed? |
|---|---|
| Move batch0 before semantic/opening/query prefix to mimic bare dV | YES. Sorting/selection use q from eight squeeze answers; rho/Prepared/claims and checkpoint state also depend on preceding challenge answers. Leaf bytes for a fixed pos are answer-independent, but the issued pos/order is adaptive. Parent inputs depend on computed leaves/lower parents. |
| Move semantic/opening absorbs past their preceding advance/init/reseed | YES. Their first32 bytes are that returned state. Semantic checks also determine whether later rows are reached. |
| Swap squeeze and advance at one fixed absorbed state | NO input dependency between these two calls: both inputs are fixed by the absorb answer. Their outputs and downstream scan/state still matter. No swap is actually required here. |
| Move later query pairs before preceding advances | YES. Pair j's input state is the previous advance answer. Its squeeze answer does not determine the next pair's address, but affects chosen q and selected output state. |
| Move S/P raw checkpoint hashes earlier, with original bytes retained | NO direct dependence of their inputs on previous verifier answers; their *reachability* depends on successful prior operations. Adversarial prequeries/retries remain relevant. |
| Move checkpoint checksum before S/P hashes or preparation/ten-query accumulation | YES. Body embeds H(S),H(P), full Prepared state and reached accumulator. Neither length equality nor pure serializer code makes it nonadaptive. |
| Move resume checksum/public/proof calls or batch1 before checkpoint save | Repeated raw S/P inputs fixed on the retained pair; checksum requires the saved body; batch1 selection uses checkpoint q/roots. The source's resume calls do not recompute transcript sampling. No movement licensed. |
| Delete extra query pairs after scan completion | Their answers do not change the already selected q/state, but their addresses depend on preceding advances and they change the shared log/table/first-read history. Model also retains them; deletion is unnecessary. |

`LogA_Dependencies.query_states_agree` checks the actual `QuerySampler.state`
recurrence: equal advance-domain answers give equal pair states, without any
squeeze-domain agreement. `plain_inputs` checks actual plain sampler input
order; `leaf_first` checks the fixed-pos address; `checksum_input_agree` requires
agreement on both digest answers as well as fixed p/a. These are local dependency
facts, not arbitrary-world permutation lemmas or native acceptance theorems.

### What tag separation does and does not establish

`LogA_Tags.prefix_free` checks pairwise prefix-freeness of the three literal
ASCII domains and fixed Merkle tags `[10,71]`, `[10,f1]`, `[10,72]`, `[12]`
(hex notation here). It includes the FULL ASCII strings: the semantic/opening
domains share an initial ASCII prefix but neither whole tag prefixes the other.
`semantic_domain` equates the actual installed source semantic constant with
`PublicInitFrame.domain`. `fixed_prefix_injective` checks injectivity in suffix
bytes; `squeeze_advance_separate` checks01/02 separation; and
`short_absorb_separate` uses real32-byte states to separate33-byte short calls
from state-prefixed absorbs. This proves the requested small tag/shape facts.

It does **not** establish global independence of all query families. Duplex
states are arbitrary32-byte oracle outputs, not globally reserved leading tags.
Proof/public hashes are untagged. Arbitrary adversary queries can coincide with
honest addresses; cached answers, repeated states and collisions need the actual
memoized oracle law and its existing bad-event accounting. “Domain-separated
extra queries have independent answers” is valid only for distinct fresh cells
under a proved coupling, not from these local tag facts alone.

## What the adopted security proof actually needs from order

`OraclePortHeadlineFrozen2PerAttempt.final_soundness` delegates the extractor
cost/relation claims to `OraclePortHeadlineFrozen2.final_soundness`, then uses
`Frozen2StartChargeProbability.failure_bound` and
`OraclePortFrozen2Join.runtime_transport`. Its hypotheses remain
`AcceptedRunJoin D rust` **and** `StoredCarrierBinding D rust P runtime`.
The former requires exact accepted verifier views AND exact accepted annotated
two-pass views, including logs. The latter binds the runtime carrier. None is
instantiated by this report.

The extractor does not intrinsically consume the entire log as an opaque ordered
sequence. `RawCutWordsFromRunExecutableBin.wordsFromRun` replays commitment
frames0,2,30, recovers maps at their **first-read cuts**, and produces29 initial
words and a folded final word. `RawCutWordsFromRunPublicValidBin.runDecodedPublic`
parses the semantic public. `OraclePortRefineJoin.RecoveredInputAgreement`
requires precisely decoded-public equality, initial-word equality and final-word
equality; `extractor_eq_of_recovered_inputs` proves this suffices for equal
extractions for every coin tape. It does not derive these equalities from
permutation, acceptance or equal roots. A leaf moved across a commitment's first
read can alter the available recovery table even when all final answers agree.
The actual costed extractor also needs its log/cut traversal cost budget; value
equality alone is not the inherited concrete cost theorem.

The probability proof uses the memoized shared-oracle experiment, not independent
per-call coins. `Frozen2StartChargePrefix.chronological_prefix` shows that the
prover plus followed sampler is an actual prefix of the full recorded run.
`first_start_before_terminal` preserves the earliest index of already followed
starts; `transcript_start_read` puts every submitted chain start in that prefix.
These feed the **Q+34** restricted start bound and the clean-acceptance argument.
Collisions are still charged over **Q+1161** distinct reads, including terminal
Merkle/checkpoint calls. Annotation's second pass introduces repeated issued
calls but no new oracle cells (`OraclePortStoredExperimentC4.first_reads`).
Canonical/enriched row metadata preserves the submitted bytes and sampler,
but its recovered words must still correspond to the actual source log.

The endpoint's explicit bound is

    failure <= (Q+34)*B + kappa(Q+1161) + 2^-126 + 2^-454,

with the stated Qmax range yielding `(Q+1)*2^-100`. The exponent claim is
conditional on the endpoint's source/runtime joins. The 2^-126 term covers
the retained extractor bank-abort allowance; 2^-454 covers query-scan exhaustion.
Do not turn the model's115 prefix calls into115 newly chargeable starts:
its decoder-start count is34, and the first-read/injection proof is material.
Do not replace the actual1921 source accounting with1161 without a proof.

A sufficient weaker future transport could use event domination plus recovered
input agreement and a proved cost bound, under the actual oracle law, rather
than strict whole-log equality. Section4 of AGENTS permits the weakest adequate
refinement; it does not permit assuming that such a transport exists.

## Options, size and risks

Estimates below are **engineering estimates of additional focused targets and
worker-days**, not measured compile time or delivery promises. They cover the
alignment/model portion only; all existing SDK/runtime/caller/child, source-to-ELF
and other soundness-cone obligations remain. No transport or frozen3 is built.

### A — source-program transport to the existing frozen2

Target the **complete verifier**, not bare dV. Derive its sampler and batch
inputs from the exact RawJ native pair; preserve all first-read commitment cuts
and recovered words; account for the physical public hash and changed checksum
addresses. Construct a coupling/simulation with a shared memo table on arbitrary
byte addresses and prequeries. Preserve accepted failure and extractor outputs,
prove the cost allowance, then lift through the two-pass compiler and runtime.
Domain-separated extra cells can receive independent answers only when fresh;
existing answers and rejected prefixes must be preserved. No actual reordering
is needed in the inspected full schedule. If a different extraction order is
chosen, use the dependency table; moving batches before sampling is adaptive.

Estimated20–40 small targets,10–20 worker-days, high variance. The apparently
simple first-head fix is not the difficult part; the oracle-dependent checkpoint
map and first-read recovery are. A universal injection on all shared addresses
has not been supplied and semantic projection is not injective on full carriers.
A transport theorem may be harder to maintain than a small exact model change.

Explicit loss accounting must take the form

    failure_source(Q) <= (Q+c_start)*B
      + kappa(Q+c_distinct) + 2^-126 + 2^-454 + delta_transport,

with a justified valid range and extractor-cost parameter, not silently inherited
constants. If source and model share all other addresses and fields, their
single-pass union adds at most two potentially fresh cells to the model log:
H(P) and the source checksum (each repeated at resume). Thus1163 is a **candidate
union budget**, not a checked source bound. H(U) and model checksum also need to
be simulated when starting from the source. Whether these cells add classifier
starts, collision cross-events or alter cuts must be proved; delta is not set
to zero here. In the general unresolved source-refinement class, use the retained
1921 source envelope rather than that conditional count. Recheck the100-bit
inequality and Qmax if any constant/loss changes. No independence assumption or
new cryptographic trust item is authorized.

### B — frozen3 in exact source order and carriers (recommended)

Keep frozen2's **full** sampler-first schedule, including all eight query pairs,
then batch0, write/read checkpoint, batch1 and finish. Add an explicit physical
public carrier alongside semantic public U, connect it to the original ASF8
statement/reconstructed TX2 bytes, and pass it to checkpoint write/resume.
Keep the two public carriers distinct at the types/interface level. Retain error
prefixes, duplicate digest handling and source-native checkpoint provenance.
The model change must be followed by an actual-source join; it is not closure
by model editing.

Estimated8–16 model/probability targets,4–8 worker-days, plus the independent
source-join work common to A/B (roughly another10–25 focused integration targets,
1–3 weeks, depending on concurrent child deliveries). These figures are not a
resource request. Build a tiny composed prototype before broad rollout.

Reusable mathematical pieces: semantic/folding/accumulator relations and density
bounds, literal sampler/decoders, byte/Merkle collision lemmas, frozen binary slot
runner and its resource/path recovery proofs, checkpoint body serializer and
write/resume laws **already parameterized by arbitrary pub bytes**, concrete
GS extractor/relation/cost ledger machinery. Re-prove the decision wrapper,
accepted checks and recovered-input agreement, annotated carrier/projection
laws, and the runtime join on the new carrier. Re-establish Q+34 charged-prefix
and Q+1161/2322 budgets for the exact new experiment; use their current proofs as
templates, not theorem-name-based attribution. Physical P may itself be an
adversary-prequeried address, so both collision accounting and extractor cut
stability still need an explicit proof. Costed extraction must use the actual
log bound.

The likely call-count constants stay unchanged because P replaces U at the
same call sites, with the same three checkpoint calls. That is an architectural
expectation, **not** a proved security bound or proof that arbitrary-address
cross-collisions are unchanged. Frozen3 must close the source carrier mismatch
and then compose, without silently assuming a physical-to-semantic equality.
No verifier/prover byte or CU change is needed for this option.

### C — change verifier/protocol bytes to match frozen2

A pure “put batch0 first” edit is infeasible with the same protocol: q and its
sorting are not available until Fiat–Shamir sampling completes. Accepting an
unbound prover-supplied q would change the security experiment. Computing the
transcript early and hiding its hash calls does not change real query order.
Changing commitment/challenge order, messages, domains or sampling changes
Fiat–Shamir challenges and entails prover changes, new proof fixtures and a
new soundness analysis. This is not a source-order optimization.

The narrow useful C variant would keep the current full order and change
checkpointing from H(P) to H(U), with explicit semantic serialization at TX2.
That changes checkpoint bytes and drops direct binding of the extra physical
public metadata; caller/account binding must replace whatever protection is
lost. The source and model would still need their complete source join.
If only that checkpoint hash input changes, Fiat–Shamir challenges need not
change (they already use U), but checkpoint producers/consumers and prover/test
harnesses that run them must change together. If the transcript itself changes,
prover challenge derivation must change too. These are distinct variants.

Estimated12–25 source/model/integration targets,1–3 weeks for the narrow variant;
true challenge-order redesign is a new protocol campaign with no defensible
small estimate. Source change invalidates the covered Kani/Aeneas/source-helper
and checkpoint/binary equivalence evidence; reproduce all three ELFs and replace
the pins only after owner adoption and relevant gates. The frozen pin values
cannot be carried across different verifier bytes.

CU: no measured delta is claimed. A same-multiset reordering changes zero hash
call counts but can change allocation/borrow/lifetime costs. P->U keeps call
counts/checksum lengths but hashes425 or453 fewer public bytes at each of two
checkpoint public calls (850/906 fewer bytes per pair); producing/decoding U at
resume costs work and may outweigh that reduction. Revised Fiat–Shamir designs
could require extra hashing/state retention. Benchmark the exact adopted ELF;
byte counts are not a CU estimate or formal cost theorem.

### Owner decision and first deliverable

Recommend B's explicit two-public-carrier model. It corrects a concrete execution
mismatch with no protocol byte change, while preserving the existing sampler's
causal prefix. It follows AGENTS §4 (actual query behavior, weakest sufficient
refinement with proved experiment/extractor correspondence) and §6 (frozen
source/artifacts unchanged, feasible proof-friendly architecture, candidate
separate until gates pass). The100-bit target remains fixed.

Next concrete deliverable: a separately prefixed frozen3 candidate with the
physical public carrier, one checked checkpoint write/resume schedule theorem,
and a small accepted same-native-pair composition into the complete verifier
interface. Then rebuild its probability/extractor dependency closure under the
same caps. Stop before more wrapper work if the exact carrier join cannot be
inhabited. No owner adoption is implied by this recommendation.

## Validation, freeze and handoff

Four new modules only: [LogA_Tags](../lean/LogA_Tags.lean),
[LogA_Dependencies](../lean/LogA_Dependencies.lean),
[LogA_PublicBytes](../lean/LogA_PublicBytes.lean), and
[LogA_Audit](../lean/LogA_Audit.lean). Twelve local mathematical facts are
checked; the schedule inventory, alignment classification, size estimates and
recommendation are source analysis, not a proved transport.

Successful focused attempts004/006/008 compile the exact committed theorem
sources. Final009 imports them and prints all twelve axioms reports. Every
accepted report is a subset of `{propext, Classical.choice, Quot.sound}` (one
requires none). Attempts001/002/003/005/007 are excluded elaboration/syntax
failures; their complete errors and source snapshots remain in the packet.
Recovery `sorryAx` lines in failed elaborations are not accepted evidence.
Budget: **9/40 Lean attempts,0/0 Kani**. No timeout/memory kill/cap raise,
unchanged resource-failure rerun, arithmetic release gate or package replay.

| Accepted target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| LogA_Tags.lean | 004 | 0 | 2.127608 | 5209472 | 0 |
| LogA_Dependencies.lean | 006 | 0 | 1.946957 | 5205776 | 0 |
| LogA_PublicBytes.lean | 008 | 0 | 2.088834 | 5204448 | 0 |
| LogA_Audit.lean | 009 | 0 | 1.775738 | 5183240 | 0 |

All attempts used the unchanged S2W launchers in the coherent workspace
`/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`, Lean4.32.0,
`lake env lean -j1 -M7000 -DElab.async=false`, one module in its own
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 scope. Initial inventory
showed only init.scope; jobs here were sequential. Final scope inventory is
retained. No build/launcher/monitor infrastructure changed.

Revision anchor is `5a46a7e2392ce5dbdddce172d3fe513a3690479b` on
`codex/cx-log-align-20261026`; theorem development receipts anchor stage0
`f28b617117`, final audit anchors stage1 `0c706a021e`, each with dirty new
source snapshots and exact source SHA. Every attempt's exact command, target,
source hash/revision, direct dependency object/sidecar fingerprint, exit,
wall/RSS/swap, cgroup limits, full stdout and axioms are in
[evidence/log-align-20261026](../evidence/log-align-20261026/).
[LogA_attempts.jsonl](../evidence/log-align-20261026/LogA_attempts.jsonl)
consolidates receipts. [Source pins](../evidence/log-align-20261026/LogA_source-pins.json)
cover the inspected runtime/model/log sources.125 reused RawJ_/RawK_/SdkD_
host source hashes match this worktree; inherited SInt2 object/cache provenance
is reused. This is focused verification, not a coherent frozen release rebuild.

No shipped file or cfg(kani) harness changed; no Rust/SBF/ELF rebuild trigger
fired. Default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
and Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`
are inherited pins, not reproduced or newly validated. Private-leaf-salts P3,
S2 variant/tag02,33 transcript rows,22 queries, split10/12, binary height18,
proof57607/checkpoint1768 and existing wire/features remain unchanged.

No assumptions discharged from the release ledger; no security/crypto/trust
assumption added. SDK/std/runtime/extraction/source-helper/child laws and
same-account/checkpoint history provenance stay retained. Native accepted-pair
source/model refinement, probability/cost transport, source-to-release-artifact
composition and the100-bit conclusion remain open. No session A worktree,
other worker prefix, key or fund was modified. Stage commits are local; no push.
