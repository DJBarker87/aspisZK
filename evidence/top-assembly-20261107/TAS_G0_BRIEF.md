# G0 final host assembly brief (split-B top)

Target not yet established. This brief sets up the Codex job that assembles the real top theorem on the build host. The theorem has the split-B form the owner approved on 2026-11-07. The job credits no row and changes no trust row, security metric or frozen source. Its output is either the assembled top theorem, passed through the gate in section 7, or a precise list of the fields whose deliverables are not yet available, plus a conditional assembly that shows everything else composes.

Base: `research` at the merge that contains this file. RSL is at Revision 2 (be66076856e). The stand-in stack compiles locally against it: TCK, TAS, TFM, EVB, TAS_TopB and TAS_TopB_NNE (rev2/REV2_LOCAL_COMPILE.tsv, 59 of 60 files exit 0; the one failure is the expected unpatched NMV_NoWritePool, repaired in phase C).

## 0. Binding rules

Read these first. They bind the job.

1. AGENTS.md, all of it, including the resource policy and section 3 (audit statements, not names).
2. C3-BIN-20261021.md, newest entries: rulings (bk) to (bo), and the owner decision of 2026-11-07 with its binding conditions on Realizes. The five conditions are restated in TAS_TopB.lean's header, together with where each is met.
3. RSL_REVISION2.md. The specs that changed are the owned getters, `verifierCheckpoint`, `S1Lib.decodeReachesAlloc`, both `mapVErr`s, and the Refs of 345/328/241/242/233/234 and their inheritors.
4. The interface files: TAS_Interfaces.lean (fields), TFM_TopExact.lean (`Split`), EVB_EventB.lean (`RecSig`, `RecSelect`, `NNC_NMFPrimeB`, `HeadlineB`, `top_splitB_full`, `no_second_charge`), TAS_TopB.lean (`ExecB`, `ctxB`, `top_splitB`, `deployed_charge`), and TAS_TopB_NNE.lean (`top_splitB_counts`, `top_splitB_physical`).
5. Never assume a field. A field is instantiated by a delivered term whose type is the field's type, or it is listed as missing (section 4). Never add a hypothesis to the final theorem to stand in for a field. Never fix the adversary `a`, in particular never to a constant adversary. Never condition on Realizes, and never use it as a filter.

## 1. Target theorem

The final theorem is `AspisR1.TAS_FinalB.deployed_splitB`. It is `RSL.TASB.top_splitB_physical` instantiated at the host `Sig`, `RecSig`, `ExecB` and libraries. Its conclusion has three parts: `C5num ∧ (the other ten conjuncts of AspisR1.RPx_Deployed.deployed, unchanged) ∧ (Outcome(…, bad := E_rec) ∨ E_rec)`. It holds at `ctxB X fx w H`: the binder block whose pair `e1 data1 state1 / e2 data2 slot state2` is the adversary's output at H (`(eval H a.first).2` and `(eval H (a.second … saved post1 final1)).2`). `realizes` is discharged by `⟨rfl, rfl⟩` inside the proof. It is not a premise.

The averaged theorem is `AspisR1.TAS_FinalB.deployed_charge`, the host form of `RSL.TASB.deployed_charge`. It bounds the mean over all H of `max r 1_{Runs ∧ ¬OutcomeRec}` by `total (Q0+Q1)`, with E_rec charged once. It uses `F3U_Averaging.charge`'s method, as in section 3, step 10.

Statement audit (record before and after, AGENTS.md section 3). Compared with `RPx_Deployed.deployed`:
- Instantiated, not assumed: `native1/2 := stage1_owned/stage2_owned (sdk c)`, `A := Bool`, `allocator := abortIndicator`, `state/final := true` (ruling (bo)), `missing := NND_Missing.instance` (ruling (s)), and the pair, from the adversary's execution.
- Derived, no longer hypotheses: `extraction`, `accepted1`, `accepted2`, `game`.
- Added as the attack's antecedent: `Runs` (frame, trace, ok1, out1, ok2, out2).
- Weakened: conjunct 4 to `OutcomeRec ∨ E_rec`.
- Retained unchanged: `queries` (L154), every runtime admission, `RuntimePersistence`, p1, syscall, std and copy.

Confirm in writing that there is no Root0 hypothesis, no hash-injectivity premise, no new trust row, and no Realizes premise.

## 2. Module list

Workspace: the pinned ledger25 workspace. Prepend NMQ_EXPORT (`/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NMQ_20261111/NMQ_exports_20261111`) to NMQ_PATHS.json, then import `NMQ_COMBINED_IMPORT`, which is ledger24 NLX + NMN + NMF + `AspisR1.RPx_Deployed.deployed`. Do not rebuild unchanged ledger modules (AGENTS.md resource rule 6).

Add the following, each at the named source, and record the source sha256 and object sha256 of every module.

| Group | Modules | Source |
|---|---|---|
| RSL rev2 | RSL_Base, RSL_Pool, RSL_TX2_{217,234,233,242,241,240,221,213}, RSL_Verifier, RSL_TX1_{136,137,087,094,328,345,344,333,330} (20, in this order) | evidence/rowspec-lead-20261107 at be66076856e |
| Stand-in stack | TCK_WeakRoot0, TAS_Interfaces, TAS_Top, TFM_TopExact, EVB_EventB, TAS_TopB, TAS_TopB_NNE, TAS_Rev2Support | top-check-20261107, top-assembly-20261107 (+ rev2/), top-form-20261107, event-b-20261107 |
| NMV_ (merged) | the 40 proof modules of NMV_EXPORT.json `proof_modules`, via NMV_BN_COMBINED_IMPORT | evidence/stage-wrap-20261111; NMV_NoWritePool/NoWriteOwned/NoWrite241 with rev2/NMV_REV2_NOWRITE.patch applied (section 5) |
| NNF_ (merged) | NNF_Carrier, NNF_Dispatch, NNF_Reify, NNF_Folds, NNF_TAS (+ NMW_Branches from its seed) | evidence/entry-rsl-20261111; export `/home/dombarker/project-offloads/codex-cx-entry-rsl-20261111/NNF_exports_20261111` |
| NNE_ (merged) | the NNE_ proof modules in NNE_EXPORT_MODULES.json. NNE_TopSplit/NNE_PhysicalTop may be imported, but they are not consumed: they are TFM form and superseded by TAS_TopB_NNE | evidence/phys-adapter-20261111; export `/home/dombarker/project-offloads/codex-cx-phys-adapter-20261111/NNE_exports_20261111` |
| NNC_ (merged + B amendment) | the 24 modules of NNC_COMBINED_IMPORT, with NNC_RSLAuth and NNC_RSLReads repaired (section 5), plus the B-amended NNC_BindingRoot/NNC_NMFPrime (or new modules) once NNC_ delivers them | evidence/root0-weak-20261111; export `/home/dombarker/project-offloads/codex-cx-root0-weak-20261111/NNC_exports_20261111` |
| NMS_ step facts | NMS_RSLRefine, NMS_RSLStepFacts at NMS_'s rev2 commit (not the pre-rev2 seed copy in NNC_NMS_SEED.json) | NMS_ branch |
| Running jobs | NND_ (A1, A2, NND_Missing), NMM_ (217, 234), NMX_ (233), NMS_ (242, 241), NMT_ (094, 328, 345), NMO_ (136), NMP_ (137, 087), at their merged commits | merged evidence dirs when available |
| Unassigned B work | `RecSelect.selects` host lemma; `HeadlineB.outcomeRec` (FJv_DRelease.remove′ + FJv_DNativeAccepted copy); `Split.concl_iff` and `Split.rest` | see section 4 |
| New (this job) | TAS_FinalSig (S0, d, r, R, X, libraries, Impl), TAS_FinalB (instantiation and the two theorems), TAS_G0_COMBINED_IMPORT | this job's evidence dir |

TAS_G0_COMBINED_IMPORT imports NMQ_COMBINED_IMPORT, NMV_BN_COMBINED_IMPORT, NNF_COMBINED_IMPORT, NNE_COMBINED_IMPORT, the NNC modules, every running-job root module, TAS_TopB_NNE and TAS_FinalB.

## 3. Instantiation order

Do the steps in this order. After each step, compile only the new file (AGENTS.md workflow rule 1). Check every field type with `example : <delivered type> = <TAS field type> := rfl`. Record any representation difference as a finding. Never coerce one away.

1. **Libraries.** Define `V0 := NNC_G1a.base debug NNC_ByteCarriers.Root0 auth064`, with `VErr = verifier.Error` and `auth064` the NMN_064 law (CLOSED in ledger25). `NNC_R0Rep.assemble`'s `canonical` must then hold by `rfl`, and `NNC_G1a.assemble`'s `Impl L (base …) VL` type must match. Fix `L`, `D`, `VL`, `P` and `C` as the CLOSED instantiations named in RSL_INDEX.md. `C : S1Lib VL` now has `decodeReachesAlloc`. Define it as the function fixed by the frozen decoder (CLOSED TX1:332), and check it is the same constant NMT_'s 345 root uses.
2. **Impl.** Start from `I0`, the actual observed-semantics functions for f217, f234, f233, f242, f064, f241, f136, f137, f087, f094, f328 and f345. Then:
   - `I1 := NMV_TasRoots.implementation I0 a1 a2`. This installs the (bn) source-fission interpreters for f344 and f240. `a1 a2 : NMV_ConcreteWindows.Allocation` stay universally quantified binders of the final theorem.
   - `I := NNF_TAS.install I1`. This installs the emitted dispatcher for process and entry over I1's wrappers.

   Check by `rfl` that `I.f344 = NMV_ConcreteWindows.stage1 a1 I0.f345`, that `I.f240 = NMV_ConcreteWindows.stage2 a2 I0.f241`, and that every child field of `I` is `I0`'s. Every row root must name the same constant as the `I` field it covers.
3. **Row roots.**
   - `NMO_Root ⟨NMO_136.root⟩`
   - `NMP_Roots ⟨NMP_137.fold, NMP_087.fold⟩`
   - `NMT_Roots ⟨NMT_094.fold, NMT_328.fold, NMT_345.fold⟩`
   - `NMM_Roots ⟨NMM_217.root, NMM_234.root⟩`
   - `NMX_Root ⟨NMX_233.fold⟩`
   - `NMS_Roots ⟨NMS_242.fold, fun R0 w h r => NMS_241.root (lib V0 R0 w) h r⟩`
   - `NMN_Root ⟨NMN_064.rslRefines⟩`. This is the RSL byte-carrier transport of `NMN_064.root`. If it does not exist, the field is missing.
   - `NMV_Roots := NMV_CandidateRoots.packet L D V0 VL P C I0 a1 a2 pl`. This is stated at `I1`; check that it is accepted at `I` by `rfl`. `pl : NMV_NoWrite.PoolLaws L` must be built from the CLOSED packets of scan226, reconstruct224, encode165 and emit219 at the chosen `L`. If any law is not derivable from its CLOSED statement, list it.
   - `NMW_Roots := NNF_TAS.roots L D V0 VL P C I1`.

   The names come from TAS_WIRING.md section 3 and the merged handoffs. Where a running job delivers a different name, use its handoff and record the mapping.
4. **Sig.** Define `S0 : Sig` with the headline terms in TAS_WIRING.md section 2 (`First/Second` the Aeneas carriers, `model1/2`, `Extraction`, `Concl`, `Bound`, `Event`, `Queries`, `env1/2`, `EnvRep`, `readerHeader`, `Root0Native`). Then set `S := NNE_RecordSig.physical S0 d r`, where:
   - `d : NNE_AcceptanceSig.Data S0` has `native1/2 := id`, `d.e1 c = c.e1` and so on, the projections of the binder block. It has no free choices. Its `err` map has `invalid` proved.
   - `r : NNE_RecordSig.Data S0` has `p t u actions` from the physical CPG observations in the binder block.

   Prove `env1_rep`/`env2_rep` and check that `mkGame` is NNE's constructor. Per NNE_WIRING.md: `Out2` is `True` by definition, and `Out1` selects `saved` from the write events. Neither carries an allocator fact.
5. **NNC.**
   - `g1a := NNC_G1a.assemble S L VL debug NNC_ByteCarriers.Root0 auth064 I H d hash world r nativeRep oracle headerRep`.
   - `r0 := NNC_R0Rep.assemble S V0 rfl selected`.
   - `nmfB :=` the NNC_ B assembler targeting `RSL.EVB.NNC_NMFPrimeB S L D V0 VL P C I g1a R`.

   `nativeRep`, `headerRep`, `selected` and the B assembler's `selected/rootImage/eventImage` are installation obligations (NNC_REMAINING.md). They must be closed terms. If NNC_ has not delivered them, list them.
6. **NND.** Use `NND_A1 ⟨NND_A1.stage1_ret⟩` and `NND_A2 ⟨NND_A2.stage2_ret⟩` against the rev2 Refs. Since rev2, the 345/241 Refs have allocation abort arms. A1/A2 quantify over returned arms only, so their statements are unchanged, but their proofs must be the rev2 ones. `Exhibited` is `c.missing = NND_Missing.instance …`, and `hx` holds by `rfl` through `ExecB.exhibited_mk`.
7. **NNE.** Use `NNE_RecordSig.a3 S0 d r VL P C`, `a4 S0 d r L D V0` and `a5 S0 d r L V0 VL P C I`. The counts are `fun c => NNE_EntryArgs.count _ 3 _ _` and `_ 7 _ _`. No `NNE_EntryRep` is needed, because `top_splitB_counts` derives the routes.
8. **Headline and B fields.**
   - `Headline ⟨deployed, numeric⟩` as in TAS_WIRING.md section 3.
   - `A0_Digest ⟨fun c hx => ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, digestSource c hx⟩⟩`.
   - `Split ⟨Rest, Outcome, concl_iff, rest⟩`, as TFM_TopExact describes. `concl_iff` is propositional reassociation. `rest` is FJp_ARCore's non-Outcome branch terms, which take no `accepted2`.
   - `R : RecSig S`, with `Realizes`, `EventRec := E_rec` (verbatim from `FJp_Mass.bounded`) and `SelectsPair`, as in EVB_EventB.
   - `rs : RecSelect S R` and `hb : HeadlineB S R`.
9. **ExecB.**
   - `Fixed` holds the oracle-free, pair-free binders (L sdk copy std, allocator := abortIndicator, missing := NND_Missing.instance, indexError, reservation, hashv, admissions, sha256, p1, syscall, root, length, prior, words, D, `a`, Q0, Q1).
   - `World` holds saved, post1, final1, post2, final2, p, t, u, actions and RuntimePersistence.
   - `first fx H := (eval H a.first).2`, and `second fx w H i := (eval H (a.second i saved post1 final1)).2`.
   - `build` is the binder-block constructor.
   - `realizes_mk`, `exhibited_mk`, `queries_mk` and `eventRec_mk` must each be `Iff.rfl`, `rfl` or `id`. If any needs more than that, report it. Do not prove it under extra hypotheses.

   Then `deployed_splitB := RSL.TASB.top_splitB_physical … X fx w H queries run`, unfolded with `show`/`simp only` to the real headline terms.
10. **Averaging (AVG).** Produce the host `deployed_charge` with `Ex.E := lazyMean J emptyTable`, where `J` is a joint program (in the style of `F3U_Joint.program`) of the account run, the runtime and the recorder. Its view must determine the pair, the `World` binders, `Runs` and `OutcomeRec` at `ctxB`.
    - First prove the view factorisation: the per-world loss `max r 1_{Runs ∧ ¬OutcomeRec}` equals `f (eval H J)` for an explicit `f`. Show also that `first`/`second` are read from that view, through the eval-of-bind lemma. That second fact is a lemma, not `rfl`, and it does not affect Realizes, which stays `rfl` at `ctxB`.
    - Then apply `AllAddressFiatShamir.lazyMean_mono_of_eval`, `lazyMean_add` and the existing `failureModel ≤ total (Q0+Q1)` chain as `budget`.
    - If some `World` binder is not a function of a program view, stop and report which one. Do not average over an H-function that is not a program view.

## 4. When a field's deliverable is missing or still a parameterized fold

TAS fields are themselves folds: a field whose type takes child RowSpecs, such as `NMV_Roots.r344 : RowSpec_345 → RowSpec_344`, is satisfied by the fold. A deliverable fails to fill its field in two cases:
- (a) it does not exist at a merged commit;
- (b) its type has extra parameters beyond the field's type, and those parameters are not closed terms or host `rfl` facts.

Examples of (b) at today's merged state:
- `NNC_G1a.assemble` needs `nativeRep` and `headerRep`.
- `NNC_NMFPrime.assemble` needs `selected`, `rootImage` and `eventImage`, and it is not yet B-form.
- `NNC_R0Rep.assemble` needs `selected`.
- `NMV_CandidateRoots.packet` needs `pl`.
- A row root may still take a child RowSpec that the TAS spine does not supply. Leaf fields r217, r234 and r136 must have no RowSpec parameter.

In either case:
1. Stop working on that field. Do not instantiate the parameter with a variable, `sorry`, a new hypothesis of the final theorem, or a trust row, and do not weaken the field.
2. List the field in `TAS_G0_MISSING.json`, one record each: TAS field, expected deliverable and owner, what exists (name, commit, exact type), the exact extra parameters, and why each is not discharged.
3. Continue with every other field.
4. Compile `AspisR1.TAS_FinalB.deployed_splitB_conditional`: the same instantiation, with each missing field as an explicit structure argument of exactly its TAS type, and nothing else. Label it CONDITIONAL in its docstring and in every report. It shows that the rest composes. It is not the top and it is never credited.

Expected missing at the time of writing:
- the NNC B amendment and NNC's three installations;
- RecSelect and HeadlineB (no job is assigned yet);
- Split.rest, unless this job proves it from the terms TFM_TopExact lists;
- NND A1/A2;
- NMN_064.rslRefines;
- PoolLaws;
- the canonical candidates of NMT_ (345), NMS_ (241/242), NMM_, NMX_, NMO_ and NMP_.

Re-check each of these at launch. Never assume one.

## 5. RSL Revision 2 repairs this job applies (statements unchanged)

rev2/REV2_IMPACT.md gives the rev2 impact decision for every merged module. For G0, these are the edits.

- **NMV_ (NMV_NoWritePool, NMV_NoWriteOwned, NMV_NoWrite241).** Apply rev2/NMV_REV2_NOWRITE.patch verbatim. It adds `ofCloned_free`, `data_free`, `dataLen_free` and `verifierCheckpoint_free`, and adds them to the `free_steps`/`owned_free` macros. It replaces `ofExcept_free` with `data_free` at the owned getter sites of 242 and 241, and adds the `format!` allocation step to `error_free`. The theorem statements are unchanged. Locally verified: the patched three plus NMV_G2Reference, NMV_TasRoots and NMV_CandidateRoots compile against rev2 with standard axioms only (rev2/REV2_LOCAL_COMPILE.tsv, phase C). Record the old and new source hashes.
- **NNC_RSLReads.from_reference.** Replace the last two bullets, `exact ofExcept_return _ _ _ _ read0` and `exact ofExcept_return _ _ _ _ read6`, with `exact RSL.TASRev2.data_return _ _ _ _ read0` and `... read6`, and add `import TAS_Rev2Support`. Reason: in rev2, `acc.data` is `RS.ofCloned acc.bytes`, not `RS.ofExcept`. The statement and the `Cut` structure are unchanged. `data_return` is compiled locally (propext only).
- **NNC_RSLAuth.successful.** In the `error` arm, after `unfold mapVErr at mapped`, insert `obtain ⟨_,_,_,_,mapped,_⟩ := rsbind_return _ _ _ _ _ mapped` before the existing `obtain … impossible`. This steps over the new `RS.lift Spec.alloc`. An alternative is to replace the three lines with `exact absurd mapped (RSL.TASRev2.mapVErr241_error_not_ok V error env _ _)`. The statement is unchanged. This edit was not compiled locally, because NMS_RSLStepFacts is not on `research`. Compile it first on the host.
- Everything else in NNC_, NNE_, NNF_ and NMV_ needs no rev2 change. 31 NMV_/NNE_ modules whose import closure is local compiled unchanged against rev2 (phase B). The rest either mention no changed spec, or use the changed Refs only as abstract fold parameters.

## 6. Open item that can stop the job: RZ-STATE

The owner's Realizes compares `⟨e1, data1, state1⟩` and `⟨e2, data2, slot, state2⟩` with the adversary's outputs. Ruling (bo) fixes `state1 = state2 := true`. `ART_PartialAccount.firstSyntax`/`secondSyntax` pass `i.state`/`j.state` to the model wrapper (lean/ART_PartialAccount.lean lines 16-22). At a world where the adversary outputs a state other than `true`, the host cannot satisfy both:
- If the binder block stores the adversary's state, `realizes_mk` is `Iff.rfl`. But NNE's acceptance is at state `true`, and `RecSelect.selects` fails there, because the account run's TX1 model reply is not `ok` and the selection's TX2 half is empty.
- If the binder block stores `true`, `realizes_mk` fails at those worlds, and Realizes would act as a filter.

Before step 9, the job checks this at the host. If it holds as described, the job stops before ExecB and the averaging, and records RZ-STATE in TAS_G0_MISSING.json. It does not choose a resolution, because each resolution changes the statement's quantifier structure.

The lead's recommendation goes to the owner. Treat the allocator state as part of the (bo) instantiation rather than as an attacker output. One way: state the theorem for the state-normalised adversary `a⊤`, which is `a` with both state outputs replaced by `true`, with `queries` taken on `a⊤`. The pair then still comes from the adversary's execution, and Realizes holds by an eval-of-map lemma rather than by `rfl`. The allocator state models allocation success, not a capability of the deployed attacker, so no real attack is excluded. This needs the owner's approval because it amends condition (4).

## 7. Resources and gate

Scopes:
- Every scope runs in its own systemd scope with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. Lean runs with `-M7000`. Each scope needs an admission JSON with `allowed:true` and exit 0, and at least 40 GB host free.
- The whole-host limit is six concurrent scopes ((bm)(4)(e)), within the 55 GiB host reservation.
- One aggregation scope is allowed: MemoryHigh=14G, MemoryMax=16G, MemorySwapMax=0. Use it only for the final TAS_G0_COMBINED_IMPORT compile and the raw ax2 walk of the new top. Do this only after every new file has passed in an 8G scope, and only if the 8G attempt was killed by aggregation memory. Do not use it for discovery.
- A job killed by memory pressure is never rerun unchanged with a larger cap (AGENTS.md resource rule 5).
- Budget: at most 40 Lean, link or audit scopes, 0 Kani and 0 extraction. Before each heavy step, record whether the time is expected in elaboration, kernel checking or aggregation. Crossing 24 GiB, or spending ten minutes without a new compiled target, is a mandatory stop and review.

Gate, all required for "top assembled":
1. **Raw ax2** on `deployed_splitB` and `deployed_charge`: standard axioms only (propext, Classical.choice, Quot.sound), with no `sorryAx` and no custom axiom. The raw walk is authoritative over the collector (ruling (ab′)(3)/(ax2)). Also run `#print axioms` on both.
2. **NFX scan** over the combined closure: exit 0, zero dangling references, zero canonical duplicate owners and zero import defects. Identical serialized replicas are listed separately, as ledger25 does. NNE copies NMV's RslDomain/RslFold/RslLaws/RslSnapshots (NNE_IMPORTED_NMV_*.lean.txt), and the scan must show one canonical owner for each.
3. **Combined import:** TAS_G0_COMBINED_IMPORT compiles. All predecessor statements and owners are unchanged against NMQ (count them). Every required root is raw ax2 standard-only.
4. **Statement audit** (section 1), plus the non-vacuity check from TAS_WIRING.md checklist item 8. For an arbitrary actual run, construct a `World` and the `Runs` facts from the recorded trace, and show that `TraceRep`/`GameFrame` are the physical facts and not `False`.

Record, per AGENTS.md section 6: exact target, exit status, wall time, peak RSS, swap, source revision and source/object hashes for every scope. Handoff: TAS_G0_HANDOFF.md, TAS_G0_MISSING.json, TAS_G0_AUDIT.json and TAS_G0_EXPORT.json. No push, no shipped-source edit, no trust edit, no sibling worktree. If any field is missing, report "target not yet established" and "top not assembled", with the missing list.
