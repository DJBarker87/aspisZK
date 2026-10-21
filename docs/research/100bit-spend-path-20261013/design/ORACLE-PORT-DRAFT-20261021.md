# Oracle port draft, 2026-10-21

Branch `codex/cx-oracle-port-draft-20261021`, base `71b7f0db3`.
This branch is a draft for lead/user review. It changes no existing Lean
module, deployed verifier, candidate pin or M10 instrumentation. Do not merge
it as a completed frozen-verifier soundness endpoint.

## Continuation 3 finding: parser carrier is impossible

The inherited parser decision **always rejects**: it asks a message bounded
by 3,717 bytes to contain the 57,607-byte stored proof. This is now a checked
Lean theorem, not a suspected missing join. The historical “strict parser”
results below prove properties conditional on an unreachable parse success.
They must not be read as a nonvacuous verifier implementation. No completed
`dV`, unconditional acceptance transfer, or frozen-decision headline is claimed.
See “Continuation 3: checkpoint state and carrier audit” below.

## Continuation status

The continuation adds a strict compact parser, query-selected occupied trees,
actual duplicate-digest comparisons, sparse sibling accounting, physical
checkpoint **framing**, selected typed-slot transport and generalized decoder
completion. `OraclePortPrefixHeadlineDraft.final_soundness` removes the
independent completion binder at an admitted decision, retaining
`CheckedAcceptance`. No completed frozen `dV` is asserted. The historical
status and receipts below describe the first packet; the continuation results
and remaining obligations are distinguished in “What remains, without
relabelling” and the continuation receipt summary.

## Status: partial port; frozen dV not constructed

The general oracle-decision carrier, compiler/replay, binary clean-model
consumer, saved-ten/resumed-twelve checkpoint and logical Pool transport
are ported. `AspisR1.OraclePortHeadline.final_soundness` is compiled at that
logical Pool instance. `OraclePortMultiHeadline.final_soundness` specializes
the entire conclusion to an admitted shared-multiproof **kernel**, deriving
its hash budget. The kernel is deliberately not called dV.

The requested milestone—an actual compact frozen verifier dV with only its
Rust equality and runtime boundaries remaining—**is not reached**. Two
mathematical model obligations remain visible in the endpoint:
`OraclePortConsumer.Completion` and `OraclePortConsumer.CheckedAcceptance`.
An actual wire parser/coverage/duplicate-check and selected-data transfer must
establish them. Merely renaming these obligations as Rust-equals-dV would
hide unfinished model work.

All additions have the `OraclePort` prefix. No existing Lean module, deployed
source, S-cone candidate or concurrent M10 file is modified. No merge or push
is performed. These are focused proofs against retained cached objects,
subject to the LOG D63 coherent-release distinction.

## Numeric bound

For the annotation compiler used by the binary extractor:

- sampler calls ≤115; terminal calls ≤1046; full verifier calls ≤1161;
- distinct first reads ≤Q+1161;
- recognized decoder starts ≤Q+1080;
- recorded entries ≤Q+2322, including rejection and collision runs.

The conditional draft bound is the exact rational

```text
(Q+1080)*15/2^109 + 6*(Q+1161)^2/2^256 + 2^-126 + 2^-454.
```

It is ≤(Q+1)/2^100 when

```text
32 ≤ Q ≤ 14777960484892959601791002642008314224629686649.
```

This is the checked `OracleDecisionMultiNumeric.safe_range`, with the
five-reader collision term charged once. The lower cutoff is necessary for
this conservative scalar envelope, not a claim that soundness fails for Q<32.
The old ledger must be instantiated at Qledger=Q+1161 to cover Q+2322 entries;
adequacy on the larger domain is not implied by adequacy at Q.

## Verbatim statement and premise comparison

The compiled `AspisR1.OraclePortHeadline.final_soundness` statement is:

```lean
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) (Q : Nat)
    (tape : R9PoolConcreteExperiment.Tape) (policy : R9PoolConcreteExperiment.Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO)
    (hcompletion : OraclePortConsumer.Completion D dO P (Q + 1161))
    (hchecks : OraclePortConsumer.CheckedAcceptance D dO P (Q + 1161))
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q + 1161)) :
    (∀ H : Bytes → State, (eval H (recorded D dO P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D dO P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D dO P policy) ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax →
      R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D dO P policy) ≤ (Q+1:ℚ)*(1/(2:ℚ)^100))
```

`recorded`, `Decision` and `Budget` refer to `OraclePortExperiment`.
`totalBound Q` is the envelope above and `Qmax` is the multiproof safeMax.
`Completion` is the exact `LazyInj.decodes` statement on the new recorded
program. `CheckedAcceptance` returns actual `Checks` on collision-free
accepted original runs at the new compiled rows; it is data-producing and
has sort Type, rather than merely asserting an unrelated Boolean.

The complete specialized statement is in
`evidence/oracle-port-draft-20261021/kernel-specialized-after.lean.txt` and
`lean/OraclePortMultiHeadline.lean`. Its sole deletion from the **new**
generic theorem after specialization is quoted verbatim:

```lean
(hbudget : Budget (OraclePortMultiKernel.decision cs duplicates frames))
```

`kernel-budget-deletion-only.diff` shows that deletion and no other change;
`OraclePortMultiKernel.budget` supplies the proof under the retained
`Admissible` hypothesis. This is not an old headline premise deletion.

The comparison against `SOUNDNESS-HEADLINE-20261021.md` is:

| Existing headline binder/conclusion | Draft counterpart | Signature accounting |
|---|---|---|
| `D` | `D` | Same decoder. |
| pure `d` | effectful `dO` | Different carrier; pure experiments embed by exact program equality. |
| `P` | `P` | Arbitrary prover retained. R16's separate construction uses canonical retagging, with a proved recorded-failure equality. |
| `Q` | `Q` | Same adversary issued-query parameter. |
| `tape` | `tape` | Same logical tape type. |
| `policy` | `policy` | Same Pool check policy type. |
| `hqueries` | `hqueries` | Exact same `AdversaryQueries P Q`. |
| `s` | No opaque structure in the new logical-model theorem | This changes the interface, not a weakening theorem for the old signature. |
| `evidence` | No opaque boundary evidence argument | No cryptographic/runtime/toolchain/source proposition has been proved by omitting this argument. See external boundary inventory below. |
| `source` | Data are supplied inside `hchecks` | Not shown to be a weaker replacement; the separate R16 source constructor does not establish matching/semantic data transfer. |
| `h_R16_instance` | R16 admission/source construction plus `hchecks` frontier | Constructed at the guarded canonical model only; no deletion from the old headline claimed. |
| `h_R13` | Matching field of `hchecks`; outstanding `TypedBinding` | Not discharged at frozen dV. Selected-leaf recovery alone is insufficient to infer full reader-data equality. |
| `h_R14_backend` | Pairing and residual-accumulator fields of `hchecks` | Typed model implication available; source/selected-data instantiation remains. |
| `h_R15_writer` | First-match field of `hchecks`; checkpoint matching theorem | Typed saved-ten/resumed-twelve fact is proved; compiler-data binding remains. |
| `h_R3_semantic` | Semantic field of `hchecks` | Typed equation checker supplies semantic endpoint and parsed degrees, but not yet on dV's recovered compiler data. |
| `h_Rwire_tag` | Admission's tag theorem; explicit `hcompletion` | The residual tag law is proved for admission. Complete decoder restoration on the new trace is still a model obligation. This is not a strict weakening claim. |
| `e` | `e` | Same value-correct costed extractor type. |
| `p` | `p` | Same parameter type; must allow the larger log domain. |
| `h_M10_ledger : LedgerRefinement e p Q` | `LedgerRefinement e p (Q+1161)` | Stronger size domain; no implication from the old ledger is claimed. |
| `h_M10_log_length` | Derived `OraclePortExperiment.log_length` | New model bound is Q+2322. This is not deletion-only weakening of the old Q+1161 interface. |
| No arbitrary terminal budget binder | `hbudget : Budget dO` | Necessary for arbitrary oracle programs. Derived at the admitted shared kernel, as audited above. |
| Logical Pool deployed failure | Generalized logical Pool deployed failure | Same-byte ghost construction; effectful terminal runs before full replay on resume. No equality with frozen Rust is proved. |
| Expected accepted-attempt cost | Same form, on new recorded runs | Conditional on shifted ledger adequacy. |
| Returned witness correctness | Same literal relation | Reuses the same binary extractor returned-relation theorem. |
| Additive abort allowance | Same `2^-126+2^-454 ≤ 2^-120` | Unchanged. |
| Q+34 scalar envelope | Q+1080 scalar envelope | Conservative increase; collision coefficient and B_V remain unchanged. |
| `Q ≤ old Qmax` | `32 ≤ Q ≤ old Qmax−31` | Required by the new conservative scalar bound, not rounded. |

The intended external boundary inventory is retained for source deployment:

| Existing `BoundaryEvidence` field | Meaning/status at this draft boundary |
|---|---|
| `h_P1` | SHA ROM/collision/target-preimage trust remains external. |
| `h_P2` | Ownership, permissions, locks, rollback and persistence remain runtime assumptions. |
| `h_P2_prime` | Same complete public/proof bytes at checkpoint handoff remains a runtime/source condition. |
| `h_P3` | SHA concatenation, stored-bump PDA and System semantics remain external runtime conditions. |
| `h_P4` | Runtime metadata observation remains external. |
| `h_P5` | Canonical initializer provenance remains a source obligation. |
| `h_P6` | Correct pinned proof/translation toolchain remains a release boundary. |
| `h_P7` | Source-to-SBF compilation remains a release boundary. |
| `h_R10` | Complete chronological tx1/tx2 log remains a source join. |
| `h_R22` | Wrapping/checked acceptance correspondence remains with the source-cone totality/caller work. |
| `h_R4_transport` | Reached sampler/public/prefix transport remains in frozen equality. |
| `h_R17` | Production fold geometry/table use remains in frozen equality/S7. |
| `h_R20` | Pool reconstruction/CPI handoff remains a source/caller join. |
| `h_R21` | Freeze identity remains a release boundary. |
| `h_S1` | Prepared/gamma/tx1 source refinement unchanged; concurrent owner. |
| `h_S2` | Frozen header/observer-off dispatch and actual caller binding remain source work. |
| `h_S3` | Inactive/table/classification source refinement unchanged; concurrent owner. |
| `h_S4` | Actual four_dots/batch/loop source refinement unchanged; concurrent owner. |
| `h_S5` | Canonical pairing/dot kernel caller refinement unchanged; concurrent owner. |
| `h_S6` | Same-byte caller/read binding remains external. |
| `h_S7` | Production query/accumulator simulation remains with S7 owner. |
| `h_S8` | Final accumulator/weights/residue caller refinement remains external. |
| `h_S9` | Factored S2 Libra source refinement unchanged; concurrent owner. |
| `h_S10` | Full frozen declaration inventory/release reconciliation unchanged; concurrent owner. |
| `h_M10_uniform` | No new claim about the concurrent uniform-cost endpoint is made; this draft uses the explicit shifted ledger. |

**No existing headline premise is removed or replaced.** Both old endpoint
files and their complete signatures remain byte-identical to the branch base.
`existing-headline-signature.diff` is empty; `signature-audit.json` records
zero old deletions. `full-port-signature-comparison.diff` displays the full
new-interface changes, and is deliberately not presented as a deletion-only
or strictly-weaker signature proof. In particular neither `hchecks` nor
`hcompletion` is advertised as merely a renamed Rust equality.

## Concrete decision and remaining model joins

The following pieces are now checked independently:

| Piece | New result | Exact limit |
|---|---|---|
| Oracle experiment | `OraclePortExperiment.original`, `.recorded` | The latter is the annotation compiler, not the single self-recorder. |
| Pure compatibility | `.pure_original`, `.pure_recorded` | Exact program equality with both existing binary experiments. All events/observations therefore transport by rewriting. |
| Sampler-prefix replay | `OraclePortReplay.recorded_transcript_eq` | Uses inclusion of sampler reads; never assigns arbitrary terminal bytes a legacy bounded address. |
| Commitment-cut metadata | `OraclePortWords.wordsFromRun_compiled_eq_original` | Exact cut equality, including failed recoveries; no collision premise needed for replay stability. |
| Extractor alignment | `OraclePortCleanModel.extractor_word_alignment` | On checked compiled rows, executable recovery reproduces retained binary compiler words. |
| Collision-free consumer | `OraclePortConsumer.clean_of_checks` | Requires the exact completion and checked-acceptance obligations on the new program. |
| Stored header | `OraclePortHeader.accepts_iff`, `.rejects_other_tags` | Exact length, magic `R1P3CB18`, byte-8 S2 tag, seven zero tail bytes; separate from the Public carrier. |
| Model tag | `OraclePortAdmission.accepted_tag` | The admission guard checks `Public.tag = 2`; source proof-tag/Public-tag equality is still a source adapter join. |
| R16 instance | `.accepted_instance`, `.h_R16_instance` | Constructs the exact public decode and rows 31/32 on admitted **canonical** P, with a total selected source. It does not identify that source's data with parser openings. |
| Arbitrary prover reduction | `OraclePortCanon.recorded_failure` | Canonical retagging preserves the full recorded failure mass; no adversary-domain restriction is assumed. |
| Shared kernel | `OraclePortMultiKernel.decision` | Admission around existing `OracleDecisionMultiTree.decision cs duplicates frames`; forests/frames remain parameters. |
| Shared leaf binding | `OraclePortLeafRecovery.accepted_leaf_recovery` | At the guarded compiled log, derives path success and read containment. Requires actual `OpenedAt`, width/salt and root-frame parsing premises. |
| Typed HCHECKS | `OraclePortChecks.hchecks` | Composes public/row instance fields with `D0TypedChecks.verify` on the **same compiled rows/data**. Parsing gives the ten semantic degree guards. |
| Checkpoint | `OraclePortCheckpoint.resume_matching`, `.resume_recorded` | Saves ten/resumes twelve checks; terminal reads execute on resume, then complete-verifier replay. This is a logical schedule. |
| Pool | `OraclePortPool.caller`, `.deployed_transport` | Same-byte ghost checkpoint with existing finite-support codec. Not the physical 1768-byte ABI; not source-order equality. |

### Exact genuine obstructions to the immediate composition

`OraclePortObstructions.no_universal_oracle_final_reader` proves that, even
with an effectful reader under a fixed H, no reader from the erased prefix
can equal `LiteralTranscript.vAt` on **all typed prefixes**. The two prefixes
have identical erased bytes and different hidden final words. Adding an
oracle-program result type does not make those inputs distinguishable.
This does not refute collision-conditioned binding on checked source runs.

`OraclePortObstructions.accepted_without_opened_leaves` proves a different,
operational gap in the provided multiproof primitive: six supplied trees,
sixty-six arbitrary duplicate inputs and six frames satisfy `Admissible`,
and the terminal accepts for **every H**, while `totalLeaves = 0`.
Consequently the proposed target “accepted multiproof plus its established
budget supplies every needed `OpenedAt` witness” is false at this interface.
This is not a full frozen-proof attack, not a depth-18 source example, and
not a counterexample satisfying the missing parser/coverage constraints.
`Admissible` was explicitly only an accounting condition in the prerequisite.

The source inspection confirms the missing distinction: `candidate.rs`
`batch_tree` hashes actual openings, derives sorted indices from queries,
rejects differing duplicate digests, checks the exact sibling-slot count and
zero padding, then calls `verify_in_place`. The primitive accepts lists of
forests, duplicate query bytes and frames; it does not implement those
checks. `OracleDecisionMultiBuild.build` supplies the right construction
primitive, but must be instantiated with the **parsed, selected** 10+12
query indices and 66 leaf inputs. Root and checkpoint frames must be derived
from the same reached transcript. Arbitrary frame queries are not a checkpoint
ABI. Source hashes are retained in `source-pins.json`.

The exposed typed binding target is quoted verbatim in
`typed-binding-frontier.lean.txt`. It is the remaining collision-conditioned
acceptance-to-`D0TypedChecks.verify` statement on the exact recovered compiler
rows, after constructing R16. It is **not proved**. In particular R13's data
equality concerns the full reader data, whereas shared recovery authenticates
selected openings; that transfer needs an explicit proof, not extensional
identification of an arbitrary word with an oracle-recovered word.

R13, R15, R3 and R14's model part are available from the **typed checker**
(`D0TypedChecks.accepted_matching`, `.accepted_writer`, `.accepted_semantic`,
`.accepted_backend`). They are not claimed discharged at a frozen dV.
Likewise the tag/R16 construction theorems are facts of the new admission
layer, not premise deletions from the old headline.

### What remains, without relabelling

1. **Parser and selected trees implemented; complete checkpoint join still
   open.** `OraclePortCompactDraft` checks header, canonical limbs, compact
   expansion and rows 0–32, binding byte 8 to `Public.tag`.
   `OraclePortSelectedDraft` obtains the 10+12 query positions from row 31,
   constructs the six depth-18 trees and their 66 source preimages, and uses
   the sparse level-ordered sibling frontier. `OraclePortCoverageDraft`
   proves occupancy, selected opened paths and the exact sibling count;
   fixed padding is checked before hashing. `OraclePortBatchDraft` retains
   actual leaf digests and compares duplicates, with roots derived from the
   same parsed row bytes. Physical checkpoint framing and the six stored-byte
   hash calls are separate in `OraclePortPhysicalFrameDraft`: **the body’s
   prepared/accumulator fields are not yet derived from the reached ten-query
   state or composed into this decision**. The full 66-call accounting law
   and its end-to-end terminal budget are also not yet proved. The earlier
   supplied-only counterexample is excluded by the new tree construction,
   not by renaming `Admissible`.
2. **Selected typed slots and a source-selector obstruction are proved;
   acceptance-to-typed-arithmetic transfer remains open.** Packed-map
   agreement transfers through C1/C2 and folded typed slots without asserting
   equality on unselected coordinates (`OraclePortTypedSlotsDraft`).
   `OraclePortDataChoiceDraft` proves that R16 fields ignore `.data`, and
   gives a counterexample to universal typed acceptance from those fields.
   This refutes that intermediate implication, **not** the full quoted
   `TypedBinding` target for a future completed verifier. The retained
   `source` chooser is not known to select the matching reader’s data.
   `OraclePortReaderSourceDraft.readerSource` binds data to that reader and
   preserves every R16 field; the old `TypedBinding` implies its quoted
   `ReaderBinding` replacement. Neither acceptance frontier is proved for
   the parser/batch decision. Consequently `CheckedAcceptance`, and hence
   the requested unconditional R13/R15/R3/R14 model discharge at `dV`, remain
   open. Merely adding a `ReaderBinding` premise would not complete item 2.
3. **Decoder trace transport proved; independent completion premise removed
   at the conditional admitted endpoint.**
   `OraclePortSamplerPrefixDraft.original_decodes` proves completion across
   arbitrary terminal-byte suffixes from sampler format and tag checks;
   `OraclePortCompletionDraft.completion_of_format` ports it to the annotation
   compiler’s exact enriched output. `completion_of_checks` derives precisely
   `OraclePortConsumer.Completion` from the retained `CheckedAcceptance` and
   tag law. The admitted conditional headline supplies the tag law and query
   bound. Its deletion-only diff removes the independent completion binder;
   it does **not** discharge `CheckedAcceptance` or instantiate a completed
   `dV`. No canonicality of the entire terminal log is assumed.
4. Establish the exact frozen Rust/caller/physical-checkpoint equality with
   that completed dV, including stop prefixes and runtime same-byte premises.
   `OraclePortPool.RustPoolEqualsModel` is the generalized resumed-observation
   join, not a substitute proof of items 1–3.
5. Supply M10 ledger adequacy at `Q+1161`, covering `Q+2322` entries. This
   stronger domain remains explicit; concurrent instrumentation is untouched.
6. Retain the intended P1–P7/R10/R20/R21 and S-cone source/runtime/release
   boundaries from the existing headline, and perform the lead's coherent
   frozen release replay after integration. No opaque boundary proposition
   is proved merely because the new logical theorem does not use it.

The single-source-join-plus-runtime milestone remains open. The continuation
reduces the independent decoder frontier, but checkpoint-state construction
and the acceptance-to-typed-arithmetic transfer remain mathematical work.
No endpoint at `dO := dV` is claimed, and items 4–6 remain named boundaries.

## What acceptance would mean

Accepting this branch would accept a **partial draft architecture**: an
oracle terminal, annotation replay including terminal reads, conservative
Q+1080 starts, Q+2322 size accounting, and a logical Pool checkpoint with
terminal execution on resume. It would not accept a complete dV, source
refinement, M10 closure, changed protocol, or released soundness theorem.
The user should not be asked to approve a merge as the requested completed
oracle port on the basis of this branch. The branch remains unpushed and
unmerged for the lead's review.

## Verification

Receipts are in `evidence/oracle-port-draft-20261021/manifest.json`.
Each attempt records its exact argv/target, source revision and snapshot/hash,
ordered search path/dependency fingerprint, exit, wall time, peak RSS, swaps,
complete axiom reports and errors. Lean is serialized with the shared mkdir
lock, uses the private object overlay, and runs with `-j1 -M4400
-DElab.async=false`. Failed elaborations are retained and are not proof evidence.
This is focused cached-object evidence, not a coherent frozen release replay.

The final focused audit passes: 17 modules, 71 axiom reports,
30 actual Lean invocations, nine failed elaborations, zero swaps. Every final
report is a subset of `{propext, Classical.choice, Quot.sound}`. The three
headline/consumer specialization targets are checked, and no existing module
was rebuilt or edited. No package build, Aeneas replay, certificate generation,
Rust gate, SBF rebuild or unchanged full-manifest rerun was performed.

| Module (under `lean/`) | Final attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Axiom reports |
|---|---:|---:|---:|---:|---:|---:|
| `OraclePortAdmission` | 2 | 0 | 8.323 | 3627597824 | 0 | 8 |
| `OraclePortCanon` | 2 | 0 | 7.684 | 3617554432 | 0 | 7 |
| `OraclePortCheckpoint` | 2 | 0 | 4.936 | 3632365568 | 0 | 4 |
| `OraclePortChecks` | 2 | 0 | 7.558 | 3622223872 | 0 | 2 |
| `OraclePortCleanModel` | 1 | 0 | 19.930 | 3635232768 | 0 | 10 |
| `OraclePortConsumer` | 1 | 0 | 10.602 | 3616325632 | 0 | 2 |
| `OraclePortExperiment` | 1 | 0 | 15.306 | 3618668544 | 0 | 6 |
| `OraclePortHeader` | 2 | 0 | 5.636 | 3624927232 | 0 | 4 |
| `OraclePortHeadline` | 3 | 0 | 3.397 | 3634429952 | 0 | 4 |
| `OraclePortLeafRecovery` | 1 | 0 | 3.981 | 3623321600 | 0 | 1 |
| `OraclePortMultiHeadline` | 1 | 0 | 6.131 | 3629547520 | 0 | 1 |
| `OraclePortMultiKernel` | 3 | 0 | 4.047 | 3635757056 | 0 | 5 |
| `OraclePortObstructions` | 2 | 0 | 11.841 | 3632103424 | 0 | 3 |
| `OraclePortPool` | 2 | 0 | 10.032 | 3629776896 | 0 | 4 |
| `OraclePortReplay` | 2 | 0 | 7.966 | 3612442624 | 0 | 6 |
| `OraclePortSchedule` | 1 | 0 | 4.228 | 3634020352 | 0 | 2 |
| `OraclePortWords` | 2 | 0 | 4.844 | 3622961152 | 0 | 2 |

Each table row's exact source revision (full Git SHA), source SHA-256,
exact target/argv, ordered dependency environment, dependency fingerprint,
complete `#print axioms` lines and failed-attempt diagnostics are in its
`<module>-<attempt>/receipt.json`, `command.json`, `source.lean`, `lean.log`
and `time.log`. The manifest indexes all attempts, including superseded
green checkpoints. Object files remain in the private `/tmp` overlay; only
hashes and sizes are recorded in `audit.json`.

The nine failed compiler attempts were repaired as follows:

- Replay-1: expose the `Read` projection before rewriting; replace a costly
  defeq comparison of inline experiments with a symbolic sampler-frame lemma.
- Words-1: unfold the underlying word-builder definition as well as its alias.
- Canon-1 and Admission-1: explicitly unfold the new core `original` definition
  where old pure aliases had unfolded automatically.
- Obstructions-1: replace `opaque`, a reserved Lean keyword, as an identifier.
- MultiKernel-1: expose the let-bound run and rewrite the public/proof
  projections separately.
- Checkpoint-1: close the sampler-carrier defeq explicitly and normalize the
  original-program carrier before rewriting its acceptance bit.
- Pool-1: close the identical record after simplification with reflexivity.
- Checks-1: use a definition for the data-producing `CheckedAcceptance`
  inhabitant, whose sort is Type, rather than declaring it a proposition theorem.

There were no memory kills and no raised proof or memory limits. A preflight
before Canon-1 detected a missing R16 cache overlay and invoked no compiler;
the D0 packet's retained search path was added before that actual attempt.
Header-1 was a green checkpoint; Header-2 strengthens its independent-public
observation to an explicit public tag-3 counterexample. Other superseded
green checkpoints reflect substantive endpoint/source changes. Nothing was
rerun with unchanged source and dependencies to fill a success table.

Reproduce the evidence/scope/signature audit without replaying Lean:

```sh
python3 -B docs/research/100bit-spend-path-20261013/evidence/oracle-port-draft-20261021/audit.py
```

The initial packet's deletion claim is the new specialized kernel's budget binder, for
which the before/after texts and deletion-only diff are committed. The full
old/new comparison is not a weakening proof. The documentation and receipts
intentionally report the frozen dV construction and remaining model joins as
unfinished, rather than treating the existence of a generic conditional
soundness theorem as completion of the requested port.

## Continuation: checked additions and exact limit

New modules have the distinct `OraclePort*Draft` names. The compact parser
now checks all fixed offsets, expands the 426 semantic and 29 y1 compact
values, scans canonical limbs, aligns rows 0–32 with the reached erased
transcript, and binds byte 8 to `Public.tag`. The sparse builder selects its
indices from the row-31 query result, divides folded indices by four, and
builds depth-18 trees from the 66 stored leaf preimages. Occupancy and generic
opened-path lemmas are proved without reducing a concrete depth-18 tree.
The batch executor retains its actual leaf digests, checks duplicates by
digest equality, and checks committed roots from the parsed bytes.

This continuation is not yet a completed dV. In particular physical
checkpoint construction, the typed arithmetic checker and its transfer to
compiled rows are not supplied by merely parsing bytes and authenticating
leaves. The previously quoted `TypedBinding` uses the retained R16 source
chooser; its predicate does not constrain `SourceInputs.data`. A new audit
module makes that fact explicit rather than assuming a selected opening
identifies the full reader data.

### Continuation signature accounting

The new conditional endpoint is
`OraclePortPrefixHeadlineDraft.final_soundness`, with `dO := admit core`.
It still requires the same `hqueries`, `hbudget`, `hchecks`, extractor and
shifted M10 ledger as the literal admitted specialization of
`OraclePortHeadline.final_soundness`. Its only binder deletion is:

```lean
    (hcompletion : OraclePortConsumer.Completion D (admit core) P (Q + 1161))
```

`prefix-headline-before.lean.txt`, `prefix-headline-after.lean.txt` and
`prefix-completion-deletion-only.diff` record that deletion. The audit proves
that the before text is the old generic signature with **only** the literal
admitted specialization, and that the after text is the new compiled source
signature. `completion` supplies the deleted argument from `hchecks` and the
admission tag law. This is a deletion from the new conditional architecture,
not from `R1FinalSoundnessBinPerQueryR19`; both existing headline files remain
byte-identical to the branch base.

The data-bound replacement frontier is quoted verbatim below. Its implication
from the retained `OraclePortChecks.TypedBinding` is compiled as
`typed_binding_implies_reader_binding`. `binding_pointwise_strict` shows
strictness for the underlying source predicate whenever typed acceptance is
inhabited: incrementing c0 breaks the old source equality, while rebinding
the actual reader repairs it. No nonvacuity theorem for a completed verifier
or unconditional strictness theorem across the entire prover domain is
claimed.

```lean
def ReaderBinding (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (Q : Nat) (fallback : (Bytes → State) → SourceInputs) : Prop :=
  ∀ H : Bytes → State,
    ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (eval H (recorded D (admit core) (R16CanonReduction.canon P))) →
    FS2.accepts (eval H (original D (admit core) (R16CanonReduction.canon P))) →
    D0TypedChecks.verify (compiledRows D (admit core) (R16CanonReduction.canon P) H)
      (readerSource D core P fallback H) = true

```

`readerSource` preserves all R16 fields and uses the successful matching reader
for `.data`. `checked_acceptance` constructs `CheckedAcceptance` **from an
inhabitant of ReaderBinding**. That inhabitant is not constructed here. This
replacement is therefore an audited repair of data selection, not a claim
that the requested frozen acceptance-to-checker theorem has been proved.

| Current R19 model premise | Continuation status |
|---|---|
| R16 instance | Admission constructs it; rebinding reader data preserves every field. |
| R13 full reader equality | Proved by a successful typed check, not yet by parser/batch acceptance. Selected slot agreement is proved separately. |
| R15 saved/resumed first match | Available from the typed check; physical checkpoint provenance remains uncomposed. |
| R14 model pairing/accumulator | Available from the typed check; its acceptance implication is not implemented in the parser/batch decision. |
| R3 semantic endpoint | Available from the typed equation checker and parsed degree lemmas; no acceptance-to-equations transfer is claimed here. |
| R-wire completion | Derived on the generalized trace from format/tag, or from CheckedAcceptance; no independent completion binder in the new admitted headline. |
| Frozen dV and items 4–6 | No dV endpoint; Rust/caller equality, M10 and runtime/source/release boundaries remain named, as above. |

The exact demonstrated obstruction is the implication “R16 instance fields
force typed acceptance for every selected witness.”
`r16_does_not_determine_typed_acceptance` refutes it for any instance witness
by changing only c0 if necessary. It does **not** refute the requested full
`TypedBinding` statement with all future parser and arithmetic constraints.
The actual remaining work is to prove the selected-reader arithmetic transfer
and the checkpoint-state construction, rather than to call either Rust
refinement. No false claim that those tasks are impossible is made.

### Continuation verification receipts

The continuation has 12 new modules and 48 final standard-axiom reports.
There were 31 focused invocations: 16 failed elaborations/resource attempts
and 15 green attempts (including superseded checkpoints). Every final
module is green. Process swaps are zero. All final axiom reports are subsets
of `{propext, Classical.choice, Quot.sound}`.

One attempt, `OraclePortDataChoiceDraft-3`, hit the unchanged `-M4400` cap
(peak RSS 4,689,215,488 bytes; exit -6). It was not rerun unchanged. The
concrete fold-plus-one specialization was replaced by an abstract badness
law and a scalar c0 counterexample; attempt 5 checks the stronger closed
counterexample in 5.447 seconds, peak 3,629,596,672 bytes, zero swaps.
`data-choice-resource-review.json` records the failure, exact source hashes
and replacement. The stderr memory exception is retained in `time.log` and
in the receipt errors. No proof or resource cap was raised.

| Module | Final attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Axiom reports |
|---|---:|---:|---:|---:|---:|---:|
| `OraclePortBatchDraft` | 3 | 0 | 4.826 | 3634544640 | 0 | 4 |
| `OraclePortCompactDraft` | 3 | 0 | 4.354 | 3645489152 | 0 | 3 |
| `OraclePortCompletionDraft` | 5 | 0 | 8.737 | 3623583744 | 0 | 2 |
| `OraclePortCoverageDraft` | 2 | 0 | 4.426 | 3639574528 | 0 | 6 |
| `OraclePortDataChoiceDraft` | 5 | 0 | 5.447 | 3629596672 | 0 | 6 |
| `OraclePortDuplicateBindingDraft` | 3 | 0 | 3.896 | 3617341440 | 0 | 4 |
| `OraclePortPhysicalFrameDraft` | 2 | 0 | 3.450 | 3634528256 | 0 | 4 |
| `OraclePortPrefixHeadlineDraft` | 1 | 0 | 6.930 | 3622289408 | 0 | 2 |
| `OraclePortReaderSourceDraft` | 2 | 0 | 5.242 | 3646668800 | 0 | 5 |
| `OraclePortSamplerPrefixDraft` | 2 | 0 | 4.821 | 3629826048 | 0 | 4 |
| `OraclePortSelectedDraft` | 2 | 0 | 6.720 | 3640393728 | 0 | 3 |
| `OraclePortTypedSlotsDraft` | 1 | 0 | 3.755 | 3631300608 | 0 | 5 |

Per-attempt command, source revision, source SHA-256, dependency fingerprint,
exit, wall, RSS, swaps, all axiom lines and errors are in the main manifest
and each receipt directory. Stage manifests separate parser construction,
checkpoint framing, typed-source audit and decoder completion.

The final audit is static: it verifies receipts, current source/dependency
hashes, standard axioms, scope and both signature claims. It does not rerun
an unchanged Lean manifest or claim coherent frozen-release evidence.
No existing Lean module, candidate re-pin, concurrent instrumentation,
wallet/key, Rust source or deployed artifact was edited. Nothing was pushed.

```sh
python3 -B docs/research/100bit-spend-path-20261013/evidence/oracle-port-draft-20261021/continuation-audit.py
```

## Continuation 3: checkpoint state and carrier audit

`OraclePortCheckpointStateC3` constructs the saved accumulator by running ten
steps from the initial state, retains the prepared inputs, and runs twelve
more steps on resume. `resumed_state` identifies the entire accumulator with
`QueryAccumulator.run22`; `resumed_fields` gives next, power, weights and rhs;
`finish_iff` identifies the resulting final relation with R14's `ClosedSum`.
These are symbolic proofs, not normalization of 22 concrete steps. They do
not supply the physical prepared-field encoder or its Rust refinement.

A genuine obstruction was found while checking the inherited parser's types.
`RawCutTranscriptRun.ErasedMessage.payload` carries
`SelectedTranscriptParams.Message = { bs : Bytes // bs.length ≤ 3717 }`.
`OraclePortCompactDraft.parseTerminal` attempts to parse **57607 bytes** from
that terminal message. `OraclePortTerminalCarrierAuditC3.parse_impossible`
and `.parseTerminal_impossible` prove this impossible for every terminal
message; `.batch_always_rejects` proves the inherited batch decision returns
`([], false)` for every oracle and erased prefix. Initial messages carry no
terminal bytes and cannot avoid this obstruction.

Consequently the existing parser cannot be the frozen dV. Its rejection
cannot be used to claim unconditional CheckedAcceptance, premise deletion,
or completed frozen-verifier soundness. A separate, unbounded stored-proof
carrier must reach the verifier/caller, outside the bounded sampler-message
type. Threading that carrier through a new experiment, compiler and Pool
transport is a substantive interface repair. Enlarging the sampler bound
would change the protocol, and is not an equivalent repair. Existing modules
remain untouched as required. Stage (c)'s requested nonvacuous composition
and the physical checkpoint-to-this-decision join stop at this demonstrated
obstruction; independent sparse accounting continues.

Receipts for these checks are under
`evidence/oracle-port-draft-20261021/OraclePortCheckpointStateC3-1/` and
`OraclePortTerminalCarrierAuditC3-{1,2}/`. Attempt 1 of the carrier audit had
an unresolved Option bind reduction; attempt 2 changes that local proof and
passes. Both successful audits use only standard axioms, with zero swaps.

## Continuation 3: side-by-side premise status

This table supersedes the historical status table where the inherited parser
was described as an implemented but unfinished verifier. The comparator is
the exact headline quoted in `design/SOUNDNESS-HEADLINE-20261021.md`.

| Existing headline | Continuation 3 result | Removed / added premise |
|---|---|---|
| Free pure `d` | Effectful decision carrier retained; inherited parser cannot carry the stored proof | No frozen `dV` specialization established |
| `source`, `h_R16_instance` | Existing admission constructor remains; no source witness at a nonvacuous completed verifier | No deletion |
| `h_R13` | Selected typed slot transport remains available; parser success is impossible | No deletion; acceptance-to-reader transfer still owed after carrier repair |
| `h_R15_writer` | New reached ten-step state plus twelve-step resume equals the 22-step accumulator | No deletion; physical prepared-state and selected first-match joins still owed |
| `h_R3_semantic` | `D0TypedChecks.accepted_semantic` remains available only after actual typed acceptance | No deletion |
| `h_R14_backend` | New resumed accumulator equation equals `HchecksAccumulator.ClosedSum`; pairing still needs actual acceptance | No deletion |
| `h_Rwire_tag` | Existing admission/tag and conditional completion results retained | No new deletion |
| No arbitrary effectful budget premise | Six-slot helper accounting establishes exactly 66 leaf calls and terminal envelope with six checkpoint frames | Does not identify a completed `dV` or delete the generic decision budget binder |
| `h_M10_log_length`, log domain `Q+1161` | Generic port log bound **Q+2322** | Larger recorded domain; not a weakening of the old premise |
| Existing scalar envelope `Q+34` | Generic port decoder-start envelope **Q+1080** | Conservative increase; range requires `32 ≤ Q ≤ Qmax` |
| `LedgerRefinement e p Q` | Generic port retains `LedgerRefinement e p (Q+1161)` | Stronger domain to cover Q+2322 entries; no claim about concurrent M10 work |
| Frozen Rust correspondence | Future **Rust-equals-dV join** must cover stored proof/public carrier, checkpoint ABI, execution and recorded log | Still external, and cannot be stated honestly as the only residual before carrier/model repair |
| Runtime, cryptographic and release boundaries | Retained as inventoried above | No deletion |

**Exact premise deletion count: zero.** No old theorem signature changes.
No `CheckedAcceptance` theorem derived from the inherited parser's universal
rejection is added. No new soundness headline is emitted at an all-rejecting
surrogate. A separate stored-proof input and its accounting/transport are
required before stage (c) can be attempted as a nonvacuous verifier theorem.

## Continuation 3: exact 66-leaf accounting

`OraclePortSparseLeafCountC3.leaves_card` proves by height induction that
opened leaves equal the finite set of selected indices in the subtree.
`OraclePortRepresentativeCountC3` proves that first-occurrence positions
are in bijection with distinct selected indices and that their complement
is exactly `duplicatePositions`. Thus every slot's distinct leaves plus its
duplicate calls equals its source position count, including repeated query
or folded indices. No full leaf universe is enumerated.

`OraclePortSixSlotBudgetC3.leaf_count` gives exactly **66** over all six
slots. `.six_slot_length` gives `66 + totalParents`; `.sibling_bound` gives
914; `.batch_budget` gives **1040**. `.checkpointBatch_budget` composes the
actual `writeResume` program with the six-slot execution and proves **1046**
on every oracle when padding holds (the shape-rejection case consumes zero
checkpoint hashes). With the existing 115 sampler-call bound this is 1161.
The helper inputs are still explicit parsed proof/query/checkpoint values;
the carrier obstruction prevents calling this helper the completed dV.

The three modules' final attempts are respectively 2, 3 and 1. Intermediate
failures were local elaboration errors. Representative-count attempt 2
reached simp's recursion limit by rewriting a position into a term containing
itself; attempt 3 replaces this with an abstract Boolean filter-partition
lemma. No limit was raised, no memory-cap failure occurred and no unchanged
attempt was repeated. All final axiom reports are standard; swaps are zero.
