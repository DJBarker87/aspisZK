# Oracle port draft, 2026-10-21

Branch `codex/cx-oracle-port-draft-20261021`, base `71b7f0db3`.
This branch is a draft for lead/user review. It changes no existing Lean
module, deployed verifier, candidate pin or M10 instrumentation. Do not merge
it as a completed frozen-verifier soundness endpoint.

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

1. Construct the full compact-proof parser at the erased terminal interface:
   fixed header, canonical field scans, compact expansion, precise row/public
   alignment, six occupied depth-18 trees, duplicate checks, sibling padding
   and checkpoint/resume framing. Bind the physical header tag to `Public.tag`.
2. Prove selected-leaf/typed-reader transfer at the canonical compiled rows,
   yielding the quoted `TypedBinding`, then `CheckedAcceptance`. Recovering a
   selected leaf is now proved; assembling all semantic and matching data
   from those equalities remains a mathematical model step.
3. Port sampler-prefix decoder completion to the new trace: establish
   `OraclePortConsumer.Completion`. No universal zero-terminal-start claim
   is needed or asserted. The old whole-log canonicality shortcut is invalid
   for arbitrary terminal byte reads.
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

The single-source-join-plus-runtime milestone therefore remains open. The
counterexamples stop the invalid immediate-composition items; independent
carrier, consumer, admission, recovery and Pool work was completed.

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

The only deletion claim is the new specialized kernel's budget binder, for
which the before/after texts and deletion-only diff are committed. The full
old/new comparison is not a weakening proof. The documentation and receipts
intentionally report the frozen dV construction and remaining model joins as
unfinished, rather than treating the existence of a generic conditional
soundness theorem as completion of the requested port.
