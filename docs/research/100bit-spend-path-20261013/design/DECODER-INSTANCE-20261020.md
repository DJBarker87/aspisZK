# R16 decoder instance: stopped deployment item, checked conditional interfaces

Branch `codex/cx-decoder-inst-20261020`, parent `f3a8c44cf`.
**No deployed D/d instance is established. R16 and deployed R18 remain OPEN.**
The independent interfaces below are proved. This packet does not replace the
missing instance with a free decision or a decision defined by existence of
Checks. Only new Lean modules are added; the frozen verifier is unchanged.
Paths below abbreviate `docs/research/100bit-spend-path-20261013/`, except
`crates/`, `programs/`, and the explicitly identified generic FS2 directory.

## Why the requested instance cannot yet be certified

`lean/LiteralByteProtocol.lean:27` defines D as address/table → optional
**sampler returning a prefix, message and challenge**. It is a reverse
oracle-address decoder. The strict R5 field parser has a different type:
`lean/ActualDecodeKStrictQM31Parser.lean:26` relates a sixteen-byte array to
an optional decoded field value. It cannot be used as D.

There is a precise underdetermination counterexample, rather than a claim
that a deployment map is impossible. New
`lean/DecoderInstanceBoundary.lean:31` proves `verifier D d = verifier D' d`
for arbitrary D,D'. At :37 it constructs unequal decoders (always none,
versus a constant completed sampler) with the same verifier. Thus extracting
verification behavior alone does not identify the reverse decoder. A choice
of reverse parsing algorithm and its row/address/table refinement are needed.
This is not an attack on the frozen verifier and does not show that no suitable
D exists. The existing constant-true counterexample remains applicable to any
attempt to leave d unconstrained (`lean/HchecksDecisionObstruction.lean:14`).

The pure d has type `ErasedPrefix → ErasedMessage → Bool`
(`lean/RawCutTranscriptRun.lean:61–67`). The actual source entry takes public,
compact proof, authenticated checkpoint and a hash backend
(`crates/aspis-r1-cost-probe/src/candidate.rs:327`). A serialization of those
inputs into this d-domain, and an implication from model acceptance to the
reached authenticated source execution, are not provided by the extracted
first facts. In particular the terminal extra message is `pf 33`, not the
row-32 message: generic `docs/research/v8-fs-generic-20261006/lean/FS2/Verifier.lean:22`.
Inventing a truth bit there would need its own provenance proof.

The retained stage-1 boundary is still opaque:
`lean/bridge-tx1-e5c186ba3-20261016/ExtractedTx1Model.lean:15,147` declares
and calls `B.finish`. The frozen finish extraction's translator failure and
the unmerged refactor are recorded in `design/TX1-FINISH-20261020.md` and the
lead-note addenda. This job stops the concrete-instance item at that boundary;
it neither applies the refactor nor proposes changing the verifier.

## Concrete source schedule audited

The entry is adapter `stage1` at
`programs/r1-cost-probe/src/r1_pool_adapter.rs:946`: account guards, zero
checkpoint, exact proof slice/S2 at :975–977, `first_decoded` at :981,
checkpoint-size equality and write at :982–985. The compact tx1 path is
`candidate.rs:270`: split=10, shape parse, strict canonical scan, semantic
preparation, batch-A authentication, geometry and ten queries, pending-weight
finish, then checkpoint. Its `prepare` at :256 expands compact semantic/y1
values before semantic verification and `Prepared::new`. Shape parsing at :40
checks fixed length, magic, tag 2 and zero tail; it does not decode every row.

`verifier.rs:72–88` gives opening rows 27 gamma (nonzero), 28 kappa,
29 alpha0, 30 folded-root/round1 alpha1, 31 final-message query scan,
32 empty-payload rho. Semantic rows 0–24 and circles 25–26 use the semantic
preparation path. Existing per-row source framing/block laws are precisely
those in `design/SAMPLER-ROWS-25-32-20261020.md`; returned-field transport,
query scan, full-prefix state and log correspondence remain required.

Stage 2 is `candidate.rs:327`: shape parse then `tx2_common` at :294;
resume/checkpoint guards, next=10, batch-B authentication, geometry, twelve
queries, pending-weight finish, relation view reconstruction, `finish_relation`.
At `verifier.rs:309–323`, acceptance checks first round, second round on S2,
final functional pairing, then next=22 and final-message dot = accumulator rhs.
This order is not the constructor order of the Type-valued Checks record
(`lean/LiteralAcceptanceTerminal.lean:34`); a record construction is not a
source execution proof.

## Exact compiled-run interface and all 26 fields

`DecoderInstanceBoundary.annotatedRun`, `compiledPublic`, and `compiledRows`
at `lean/DecoderInstanceBoundary.lean:16,20,24` fix the exact M9 substitution:
`eval H (experiment (compiled D d (buildWords D) P) (verifier D d))` and its
33-row transcript. No unrelated parsed prefix or original-run rows are used.
`hchecks_deployed_partial` at :72 specializes the existing reader composition
on these expressions. **D and d remain parameters**; the name denotes the
intended consumer, not a constructed deployment instance. It proves
`Nonempty (Checks compiledPublic compiledRows)`, since Checks is a Type.
No Checks or acceptance-to-Checks implication is assumed as an input.

The table records construction after the named inputs; it does not upgrade a
field to following from deployed acceptance. Missing lemma names in this
packet are requested obligations, not existing Lean constants.

| Field | Supplier after this job / remaining source obligation |
|---|---|
| decoded | Explicit carrier; accepted serializer/public selection remains R6/R9 |
| view | Constructed from matchingRead by `matching_read_parsers` (:23 in HchecksReaderComposition) |
| data | Explicit carrier; AcceptedSourceToCompiledRows must identify recovered words and payloads |
| publicParsed | `compiled_publicParsed_of_serializer` (:52): serializer success, payment guard, supplied-public binding and literal-byte equality remain inputs |
| matchingRead | `hmatching`; missing AcceptedSourceToCompiledRows through compact expansion and R12/R13 |
| openingRead | Derived from the same matchingRead; no extra premise |
| pairingChecks | `hpairing`; missing AcceptedPairing including both source relation rounds and functional identities |
| m31 | Explicit carrier; AcceptedSourceToCompiledRows must identify final-message bytes |
| queryBytes | Explicit ordered List Nat; missing source array/scan equality |
| state31 | Explicit carrier; missing scan-selected state and global-log equality |
| m32 | Explicit carrier; missing empty rho message transport |
| rho | Explicit WideExact carrier; missing source QM31 → selected rho map |
| state32 | Explicit carrier; missing source block-advance equality |
| entry31 | `h31`; missing AcceptedSourceToCompiledRows / source query-scan refinement |
| entry32 | `h32`; missing AcceptedSourceToCompiledRows / rho transport |
| valid31 | `hv31`; missing literal constructor map (erasure alone is insufficient) |
| valid32 | `hv32`; missing literal empty-payload constructor map |
| queries | Constructed with `legalOfList`, preserving order |
| queryDecode | Derived from `hq` (Nodup, length=22, all <262144); source scan must supply hq |
| firstMatch | `hfirst`; missing AuthenticatedFirstMatch for ten saved and twelve resumed queries |
| residualBatch | Derived algebraically from `haccum`; missing RestoredAccumulatorClosedSum, restored powers/weights/next/rhs and final coefficients |
| claim | Constructed from the matching reader's semantic payload 14 |
| polynomials | Constructed from its ten semantic coefficient rows |
| claimParse | Derived by the semantic parser projection facts on that same view |
| polynomialParse | Derived by the same facts on that same view |
| semanticChecks | `hsemantic`; missing LiteralSemanticEndpoint tying R2's endpoint to this public, view and data.Y |

The public supplier directly composes the landed bindings theorem through
`HchecksPublicComposition.publicParsed_of_serializer` (:13). R5's strict
parser proof is not a proof that its caller supplied these bytes. R2
`RawActualParsedFinishLiteralPrefix.parsed_finish_literal_prefix` (:21)
produces a coupled first25 prefix and a conditional polynomial chain, with
explicit `B.terminal`, mask canonicality, public-byte, digest and view-pair
premises (:32–87). It does not conclude `SemanticEndpoint` on this compiled
run. Claiming otherwise would silently discard the endpoint-identification
obligation. Therefore R2 and R5 are audited dependencies, not newly discharged
source hypotheses in this theorem.

The stage-2 first facts likewise do not have Checks conclusions:
`evidence/stage2-continuation-20261020/proofs/parse-v3/source.lean:385`
proves successful length under ParseShapeOps;
`resume-fact-v6/source.lean:31` proves proof-digest/checkpoint bytes equality
under typed ResumeOps and comparison soundness;
`facts-v3/source.lean:13` gives twelve ordered calls from next=10 under
AccumulateOps/QueryOps. None identifies compact payloads, restored fields,
word metadata or semantic endpoints. They are not imported as if they supplied
these missing fields; frozen-source backend correspondence remains owed.

## R18 and R19 results

`lean/DecoderInstanceBudgetTag.lean:17` proves the precise universal htag
shape for `experiment P (verifier D d)`, conditional on the selected parsed
public mapping for **every oracle**, including rejected runs. The landed
format work suffices for this implication, not for the deployed mapping.
It would be incorrect to assume the mapping only on accepted executions.
No unconditional deployed htag is claimed.

`hQShape` (:30) is

```
∀ H, firstReads emptyTable (eval H (experiment P (verifier D d))).1
  ≤ QP + 595 + Q2
```

Here QP conservatively bounds prover **total calls**, and Q2 bounds stage-2
total calls for all admitted executions, including rejection prefixes.
`hQ_of_complete_log_coverage` (:46) proves this from a complete accounting
partition of the experiment's log, the actual `QvStage1.CountedTrace 10`
certificate, and Q2. It uses `QvStage1.stage1Budget_ten` and the existing
firstReads ≤ length lemma. Thus the stage-1 contribution is exactly the
landed bound `43*10 + 165 = 595`, not the retired 328. This is a sufficient,
conservative hQ interface, not a new universal source-call bound. A sharper
prover-first-read interface can replace total-call accounting later.

The partition is an accounting permutation, not a source simulation: source
order, answers, complete call coverage and source-to-model transport still
belong to R10/R19/R20. Q2 is a parameter, not an estimated numeric constant.
This packet does not close R19 or instantiate M9's failure theorem.

## Verification and release limits

Receipts: `evidence/decoder-instance-20261020/manifest.json` and the
per-attempt command/source/output/time/receipt files. Final accepted attempts:

| Module | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|
| DecoderInstanceBoundary | boundary-v3 | 0 | 13.442 | 3,395,108,864 | 0 |
| DecoderInstanceBudgetTag | budget-tag-v2 | 0 | 12.209 | 3,181,903,872 | 0 |

Six theorem audits, all subsets of `{propext, Classical.choice, Quot.sound}`.
Each receipt records source revision, exact command, source SHA, direct
import-object hashes and dependency fingerprint. The checker uses the pinned
Lean 4.32 binary, `-j1 -M4400 -DElab.async=false`, the shared mkdir lock,
a process-name memory gate and private
`/tmp/codex-cx-decoder-inst-20261020-objects`. Shared objects and existing
modules are not edited. The runner refuses unchanged source/dependency
attempts. The missing Qv object search path was corrected from the landed
R19 receipt; that environment change justifies its second attempt.

Retained failed attempts are not proof evidence: boundary-v1 used a reserved
identifier; boundary-v2 had insufficient expected type in a diagnostic
Option equality; budget-tag-v1 had a missing import search path. The failed
elaboration's `sorryAx` appears only in rejected logs, never in the accepted
audits. No memory-pressure failure or cap increase occurred.

`freeze-source-check.json` records equality of both verifier source directories
with freeze revision b2727acd3. This is focused cached verification, not a
coherent fresh release build, extraction rerun or frozen-manifest replay.
No Rust gate, CU measurement, deployment, key cleanup or full regression was
needed for these new interfaces. Release C2 remains the lead's unified build.

The exact next source theorem is AcceptedSourceToCompiledRows together with
an acceptance-preserving source-input encoding into a fixed P/D/d family.
It must include authenticated checkpoint provenance and restored fields,
compact expansion, all 33 row constructors/challenges, recovered words and
same public. Only after that map exists can the named remaining field lemmas
be instantiated and this packet's conditional result become deployed R16.
