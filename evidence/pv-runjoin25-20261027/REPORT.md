# Runjoin25 — LOG D332 resume

Target not yet established. Worktree exactly `/Users/dominic/ZK/.worktrees/pv-runjoin`; branch `codex/pv-runjoin-20261026`; entry HEAD `0df6024f36`.

Step 1 fails: existing generic consumers cover a concrete non-honest native instance, even with a satisfiable original SourceIdentification. This is a further checked consumer-domain finding, not a failure of a candidate lemma. Accordingly step 2's explicit prerequisite is false: no restricted SourceIdentification was defined or substituted. Step 3 is independently checked: both original fixtures satisfy every proposed honesty guard. No endpoint or frozen implementation edit.

## Checked consumer finding

`PV_RunJoin_ConsumerBoundary25.HonestInput i` is only a diagnostic predicate:

```lean
Admission i ∧
@PV_Src_NativeInput.run E_shipped R_shipped i = ok (.Ok i.compiled) ∧
PV_Src_RecordReference.Checked i ∧
∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!
```

Here R_shipped is exactly `PV_RunJoin_UniversalRecords22.shipped` with the canonical-root table. The predicate contains semantic admission, the FULL successful returned payload with both Result layers, and both remaining guards of UniversalBuild22. It does not assert the desired public/build equality and is not a new source carrier.

Let `b := PV_RunJoin_AdmittedReturnCounterexample23.counterexample`, the admitted transfer whose cached trace.variant alone is changed. Set `inputs : Unit → Input := fun _ => b`, `source := PV_Src_NativeIdentification.prover inputs PV_Src_Transport.transport`, and `target := UniversalBuild22.toInstance inputs (fun _ => admitted)`.

Accepted38130 proves the original, UNRESTRICTED `BuilderSource.SourceIdentification source target` and `¬ HonestInput (inputs ())`. The public and build equations reuse PremiseTruth24.variant_public_eq/variant_build_eq; transport is D18. Cached trace.variant is absent from both source computations, but is part of the full compiled payload. The failure of its compiler-return association reuses the checked `not_cached_return`, not evaluation of a whole run. Admission, Checked and all frontier guards separately remain true from runjoin23. Thus this is not a vacuous identification premise.

Accepted38133 fixes `x := (source.public (), ())` and checks:

- `protocol_join_at_nonhonest`: `BuilderProtocolInstance.join_of_identification` returns its canonical-target trace/public join at w=(), together with `¬ HonestInput (inputs ())`.
- `source_sound`: `BuilderSource.builder_refinement_D46_D51` accepts the same certificate with its unchanged type.
- `consumer_at_nonhonest`: `PV_Src_Consumer.of_identification` returns `PublicBase F x.1 ∧ BuilderSoundOn source B x` at w=(), together with the same non-honesty fact, for every supplied packing basis B.
- `matching_fibre_not_honest`: the assertion `∀ w, source.public w = x.1 → HonestInput (inputs w)` is false.

The existing consumer conclusions are TRUE here. The new finding refutes the proposed assertion that all their covered instances are full compiler-associated honest inputs. It does not refute builder soundness or prove the shipped compiler emits a wrong payload. The generic theorem contracts include this non-honest w; no deployed caller is claimed to select it.

## Exact consumer audit

`consumer-use-inventory.json` enumerates every SourceIdentification/BuilderSource textual use, with lines and selected source hashes, in the endpoint's 669-project-module import closure and in the explicitly requested wider source audits. The latter include 735 project modules for PV_Src_ReleaseAudit and834 for RootDynamicIdentification. Import closure is distinguished from a theorem's actual constant dependencies. Source authority is EJR/freeze/h5 with h5' precedence, not filename search.

| Consumer / producer | Exact w or i used | What its own contract supplies; full native honesty? |
|---|---|---|
| BuilderSource.builder_refinement_D46_D51 | Every w:source.Instance with source.public w=x.1 | Uses identification.build_eq/public_eq w. No successful-return guard. FALSE in the checked singleton for honesty. |
| BuilderProtocolInstance.builder_sound | Every canonical w on x's public fibre | Canonical relation membership by subtype. No native input or compiled payload is carried. |
| BuilderProtocolInstance.join_of_identification / builder_sound_of_join | Every raw w on x's public fibre, mapping to toInstance w / existential p | No cached-payload guard. Checked protocol_join_at_nonhonest instantiates join_of_identification at (). |
| BuilderRuntimeJoin.toInstance / sourceIdentification / builder_refinement_D46_D51 | Every w:source.Instance, first constructing (publicInput w, reconstructed witness) | join.admission w, words w, publicCorr w, public_eq w and raw_trace_eq w are explicit; no native Input map or successful-return equation exists in this structure. It does not establish full native honesty. No runtime join is installed for a shipped caller. |
| PV_Src_Consumer.of_identification | Every w with matching public; calls the generic builder refinement | No extra honesty premise; consumer_at_nonhonest is the checked negative result. |
| PV_Src_Consumer.extracted_stages / forest_stages | Every i:PV_Src_Canonical.Instance on the public fibre | Delegates to the canonical stage certificates below. No native compiler association. |
| PV_Src_Consumer.existing_consumer | Every canonical w under PhaseWireLog2Bin.honest BuilderSource.prover | Uses existing canonical builder premises; consumes no SourceIdentification. |
| PV_Src_Identification.toInstance / public_eq / build_eq / identification / builderSoundOn | Every i:I; subtype proof premises.admission i | words/publicCorr/admission/row_call, for separately supplied extracted bank-stage records. Its Input has NO compiled payload, request or compiler-return guard. Not a full-native honesty theorem. |
| PV_Src_ForestIdentification (same declarations) | Every i:I with premises.admission i | Same quantifiers and guards for the forest bank-stage namespace. No full native payload in its Input. |
| PV_Src_NativeIdentification.toInstance / public_eq / build_eq / identification | Every i:I; records p i chosen from successful constructor; canonical proof p.admission i (records p i) (records_success p i) | p.compile_call i is the exact full cached successful return; p.words/publicCorr/admission apply to that SAME returned record, plus row_call. This native adapter retains the essential guards under its supplied ExternalLinear/Records dictionaries. It does not claim every raw Input has p. It does not assert the stronger Checked/frontier predicates, which are sufficient guards for the separate shipped UniversalBuild22 proof. |
| PV_Src_NativeConsumer.builder_premises / phased_builder_premises | Every i:I on the public fibre | Passes the above native identification p into of_identification; native compile/admission/record guards remain explicit. Phase adapter preserves the domain. |
| PV_Src_RootDynamicIdentification.source | Every i:I, inputs i=PV_Src_FrozenInput.input (data i) | core.compile_call/admission/row_call supply native premises. FrozenInput.checked/frontier supply representation guards. Dictionaries are external reference + computed-root dynamic records, NOT automatically the shipped dictionaries. No unconditional shipped caller association. |
| PV_Src_Canonical.identification / public_eq / build_eq | Every i:Instance, target toInstance premises i=i.canonical | canonical.property and record/public roundtrips establish the model relation; indexBound explicit. The stage encoder has no full compiler payload. No native successful-return fact is implied. |
| PV_Src_ForestCanonical.identification / public_eq / build_eq | Every i:PV_Src_Canonical.Instance, restored forest-stage records, target=i.canonical | Same canonical membership via namespace record transports; no native payload association. |
| PV_Src_ReleaseAudit | None | Only #print and #print axioms; it applies no handoff at any w. |
| PV_Src_Transport | None | Whole row-equivalence equality; no instance quantifier or cached payload. |
| PV_Src_Fixtures and fixture-only imported canonical/fibre modules | fixture b (b:Bool), or existential canonical transfer/withdrawal witnesses | Canonical semantic non-vacuity/stage trace witnesses, not full native compiler-return association. The separate original native fixtures are checked below. |

Additional uses in the actual endpoint import closure: PrivacyR1FinalProtocolBuilder's canonical theorem, PrivacyR1FinalRelease, the canonical branch of PrivacyR1Headline, PrivacyR1HeadlineDeployed, PrivacyR1HeadlineDeployedReal, ProverCommitAdmittedEndpoint, ProverCommitDeployedFuel22 and ProverCommitFixedEndpoint fix BuilderSource.prover. Their w is a canonical instance on the public fibre, with semantic membership by subtype and no raw compiled cache. They do not invoke a new honest-native SourceIdentification. The source branch `PrivacyR1FinalProtocolBuilderSource.privacy_R1_protocol_source` and `PrivacyR1Headline.builder_premises_of_source` accept RustRuntimeJoin h and use it at every arbitrary h.Instance w with matching public, with exactly the runtime-join boundary above. No hidden full compiler-return guard was found. Exact selected lines for all these uses are in the inventory.

## Statements, fixtures, and endpoint boundary

AGENTS.md §3 before/after: the original `SourceIdentification source toInstance` is unchanged:

```lean
public_eq : ∀ w : source.Instance, source.public w = BuilderSource.prover.public (toInstance w)
build_eq : ∀ w : source.Instance, source.build w = BuilderSource.prover.build (toInstance w)
transport_eq : source.transport = BuilderSource.π
```

BEFORE = AFTER, including every generic consumer's quantifiers and conclusions. No subtype replacement, added premise, or changed conclusion was applied. The proposed restriction to `{i // HonestInput i}` would change the intermediate statement and exclude the checked singleton. Step 2 is therefore not authorized by its prerequisite and was not performed. The diagnostic predicate and proofs above add facts, not a replacement contract.

`transfer_honest` and `withdrawal_honest` (38130; audited38134) prove HonestInput on each original native fixture, using named Admission, exact successful return, Checked and frontier proofs. No fixture is promoted to universal compiler success.

The endpoint is still `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`, fixed to BuilderSource.prover, with RustRealRefinement and NO SourceIdentification argument. The previous exact endpoint print is retained at `evidence/pv-runjoin24-20261027/out-38128.log`; audit38134 verifies its standard axioms alongside the new consumer findings and the existing endpoint_input_is_canonical/canonical_identification facts. The endpoint is not shown vacuous, and no raw-source privacy theorem is inferred.

## Ledger and stop

Whole ledger rows removed0. V038/V045/V047 remain; V152–V154 await the lead's stated reclassification of the jointly unsatisfiable RAW-carrier handoff. This job does not edit or invent a recount. Last supplied recount6:407 rows, OPEN86, CLOSED-ON-CANDIDATE44, types400P/3T/4C. These are the inherited figures, not a fresh post-reclassification count. Recount5's continuing boundary: “Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.”

Deployed P OPEN→OPEN; constructed P unchanged. Endpoint premises removed/added/weakened0/0/0; intermediate pre-existing statements changed0. T remains exactly entropy_law, entropy_kernel, observation. No observer, simulator, shipped source, binary, wallet or key changed. No privacy release claim.

Stop: the requested all-consumer honesty condition is checked FALSE for generic consumers that explicitly cover the non-honest singleton, while their identification premise is inhabited. The failures38129/38131/38132 were ordinary candidate elaboration failures, retained and repaired; none was the stopping reason. Remaining64/70 Lean attempts,0Kani. Next deliverable: lead adjudicates this consumer finding and selects a separate native successful-return handoff if desired, preserving the existing generic contracts and explicitly supplying every native caller's input association. Merely replacing the global certificate's carrier would not preserve all existing consumer coverage.

## Validation, pins, and receipts

6 charged host Lean attempts:3 accepted,3 rejected. Accepted38130 ConsumerBoundary25,38133 ConsumerUse25,38134 ConsumerAudit25. Every current new Lean module has an accepted snapshot matching its git source, and every new theorem has #print axioms. All accepted axioms are subsets of propext, Classical.choice, Quot.sound. Failed logs containing sorryAx are rejected, never credited. No local Lean/Kani, heavy arithmetic, timeout, kill, reservation refusal, increased cap, full manifest replay or unchanged full regression.

Requested audit IDs38194–38196 were already consumed by runjoin24, as its committed receipt index records. They were not reused. The combined new audit used next unused authorized ID38134. Used38121–38128 and retired38122 are inherited; fresh38129–38134 are used here. Remaining authorized focus IDs38135–38193. The logical remaining compile budget64 exceeds those59 remaining IDs; no further IDs were allocated because the checked step-1 finding stops this job.

All scopes sequential, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000. Peak RSS5,015,089,152bytes; all swaps0. Host wall times4.60/5.03/6.39/5.72/7.35/3.70seconds in ID order. `receipt-index.tsv`, receipt-*.json, snapshots, out/time logs record exact targets, exit statuses, wall, peak RSS, swap, source revision/blob/sha256, commands, dependency fingerprints and complete axioms.38129's collector initially requested the old pv24 log prefix; its original pv25 output and time were recovered read-only, with no resubmission, and the collector prefix corrected.

Before the first compile, all5673 actually selected external objects matched the h4/SCOPE manifest (`external-hash-check.json`). The resolved final union has1418 project modules, none unpinned. `focused-resolution.json` records EJR/freeze/h5' precedence and variant conflicts. `final-source-refresh.json` pins the3 new modules by HEAD path/blob/sha256. The final cache check has1418 matches and no unmatched source. h6 verification checks669 reused Stream B replay roots,785 transitive source/object fingerprints, and identical toolchain configuration, all matching. The private workspace and import prefix are retained from runjoin24; no shared source or another job's cache was written. This focused dependency/axioms audit is not a fresh coherent release rebuild.

Commits from entry HEAD are recorded in `commits.txt`. All commits are path-limited; no push or merge.
