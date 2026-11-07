# TAS top-assembly wiring (G0)

Target not yet established. This package closes no row and discharges no premise. It fixes the exact statement each job must hand over and shows, in Lean, that those statements compose into the headline's statement shape. Base: `research` at aec11759f86. Sources: TCK_REPORT.md, RSL_ (canonical RowSpecs), the headline `AspisR1.RPx_Deployed.deployed` (evidence/replay-deployed2-20261027/RPx_Deployed.lean), `NMF_GameRoot` (evidence/root-transport-20261110), `CPH_Game`, `CPP_Invocation`, `CPG_RuntimeTrace` and `FJv_Top` (read with `git show`). Sibling branches were read at NNC 8f4d5e9790a, NND cac9fc05e3a, NNE 57d07c80b30, NMV 5b9305e7179, NMS a72aa527f6a.

## 0. What compiles

- `TAS_Interfaces.lean` imports TCK_WeakRoot0 (and through it RSL_TX1_330), nothing else. It defines `Sig` (the headline stand-ins), `lib`/`Refines064` (G1b), `Impl` (the actual functions), one structure per deliverable, and four route lemmas over the RSL entry reference (`ref213_stage1`, `ref213_asq8`, `ref213_reject`, plus the ASQ8/stage1 data facts).
- `TAS_Top.lean` proves `RSL.TAS.top` with no sorry and no axiom. Conclusion: `S.Bound c m1 m2 ∧ (S.Concl c m1 m2 ∨ S.Event c m1)`, where `m1 := S.model1 c` and `m2 := S.model2 c`.
- Validation: three single-file compiles under `lake env lean` (TAS_COMPILE.tsv), all exit 0, peak RSS 448 MB or less, 0 swaps, 0.2 to 0.5 s each. `#print axioms` lists `propext`, `Classical.choice` and `Quot.sound` only (TAS_AXIOMS_OUTPUT.txt). RSL's 20 modules were rebuilt locally from research sources first, also exit 0 and at most 730 MB. There was no host run, no package build and no combined import.

## 1. Proof outline of `top` (all steps are in TAS_Top.lean)

1. `ext := a0.extraction c hx`, giving `extraction` at `native1/2 := model1/2`. `bound := hl.numeric …`, which is Root0-free.
2. `entryRoot R0 w h`: the 18 row folds composed bottom-up (136→137→087→094→328→345→344; 217,234→233→242→241→240; 344,240→221→213) for every library `lib V0 R0 w` whose 064 law the actual call refines.
3. `weakEntry`: with G1a's `w`, `TCK.entry_weak_unconditional` gives the entry reference for every invocation. Hence `stage1Ref`, `reject` and, with G2, `asq8Frame`.
4. A5 turns these into game (d) at the models; `S.mkGame` gives `game`. A3 turns the stage1 reference of the actual TX1 Ok run into `accepted1`. None of this uses Root0.
5. NMF′ gives `Root0Native c ∨ Ev c`.
   - Event branch: `cs.event_eq` gives the headline's event.
   - Root0 branch: R0-rep gives `TX2_240.Domain V0` at the TX2 images. The canonical `entryRoot` (via `nmn.r064`) and `ref213_asq8` then give the canonical 240 reference. A4 gives `accepted2`, and `hl.deployed` gives `Concl`.

Fact used (checked in `CPP_Invocation.native`): on the `.second` route the effect is `(store, .rollback, .inr _)`, so game (d) does not depend on native2's result. That is why A5, and therefore `game`, needs no Root0. Only `accepted2` does.

## 2. Stand-ins (`Sig` fields) and their host terms

All stand-ins are fields of one structure, not `opaque` or `axiom`. The host instantiates `Sig` once.

| Field | Host term |
|---|---|
| `Ctx` | structure over the headline binders except native1/native2/extraction/accepted1/accepted2/game/queries (list in the Sig docstring); keeps admission1/2, std, sdk, p1, syscall, RuntimePersistence as hypotheses |
| `First`, `Second` | `S2W_ExtractionBoundary.First`, `.Second` |
| `model1`, `model2` | `AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk c)`, `…stage2_owned (sdk c)` with `c := FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation` |
| `Exhibited` | `ctx.missing = NND_Missing.instance …` (ruling (s)); substitution of the binder `missing`, proved by `rfl` |
| `Extraction` | `S2W_DigestExtraction.AeneasExtraction (sdk c) n1 n2 hashv` |
| `Accepted1`, `Accepted2` | `S2W_D189Wrappers.first n1 copy allocator e1 CPH_Program.verifier data1 state1 = ok (.Ok (saved,post1,final1))`, `…second n2 allocator e2 … data2 slot state2 = ok (.Ok (post2,final2))` |
| `GameFrame` | fields (a), (b) and (c) of `CPH_Game.DeployedPairExecution`, plus `p.copied t = saved ∧ p.actions t = actions` |
| `Recorded1`, `Recorded2` | the two `CPG_RuntimeTrace.Executes …` conjuncts of (d) |
| `Game`, `mkGame` | `CPH_Game.DeployedPairExecution …`, built with its anonymous constructor |
| `Queries` | the `queries` binder (L154) |
| `Concl` | the eleven-conjunct conclusion of `deployed` |
| `Bound` | the three `F3T_RuntimeBound.failureModel runtime` conjuncts of conjunct 5 |
| `Event` | `BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P) F3X_Projection.project select))` (no native2) |
| `args1/2`, `state1/2`, `env1/2` | NNE_ carrier map: RSL Args/SdkState/Env images of `e1/data1`, `e2/data2`, `e.heap`, and the runtime oracles (`clock := .ok slot` at TX2) |
| `Out1`, `Out2` | `saved`, `post1`, `final1` (resp. `post2`, `final2`) are the carrier images of the RSL observation |
| `EnvRep`, `env1_rep`, `env2_rep` | sha256 replies through `syscall`/`p1`, PDA replies, clock = slot (RuntimeClockSlotBinding) |
| `TraceRep` | every `.invoke` in `p.actions t/u` is the runtime's execution of `entry` at the RSL images; non-verifier actions are the recorded Pool/runtime actions (Stream C) |
| `Root0Native` | `∃ s, <G1c native TX2 cut> ∧ NLP_InputDomain.Root0 s.checkpoint s.proof` |
| `readerHeader` | `NLW_ReaderHeader.decode ck = some (h pr, h pub)` with `h` from `env.sha256` |
| `ModelRet1/2` | `model1 c` (`model2 c`) at the carrier image of the RSL arguments returns the image of `r` |

## 3. Interface fields: owner, suggested name, host instantiation

Folds with a CLOSED root are supplied as `fun _ … => root`.

| TAS field | Owner | Suggested Lean name | Host instantiation |
|---|---|---|---|
| `Headline.deployed` | existing | `AspisR1.RPx_Deployed.deployed` | `fun c n1 n2 e a1 a2 g q => AspisR1.RPx_Deployed.deployed <binders of c> n1 n2 … e … a1 a2 … g … q` |
| `Headline.numeric` | existing | `FJp_Residual.numeric`, `F3U_Range.per_attempt`, `F3U_Numeric.runtime_margin` | as in FJv_Top lines 129-142, with `owners := FJu_GlobalOwners.complete _ _ (FJv_GlobalOwners.complete … (FJv_GlobalTerminal.owners missing indexError reservation _))` |
| `A0_Digest.extraction` | G0 final job | `TAS_A0.extraction` | `fun c hx => ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, TAS_A0.digestSource c hx⟩` |
| `NMM_Roots.r217` / `.r234` | NMM_ | `NMM_217.root`, `NMM_234.root` | `⟨NMM_217.root, NMM_234.root⟩` |
| `NMX_Root.r233` | NMX_ | `NMX_233.fold` | `⟨NMX_233.fold⟩` (or `fun _ _ => NMX_233.root`) |
| `NMS_Roots.r242` | NMS_ | `NMS_242.fold` | `NMS_242.fold` |
| `NMS_Roots.r241` | NMS_ (G1b) | `NMS_241.root` (∀ V with 064 refinement) | `fun R0 w h r => NMS_241.root (TAS.lib V0 R0 w) h r` |
| `NMV_Roots.r240` | NMV_ (G1b) | `NMV_240.root := fun V r a s env d => NMV_RslFold.fold240 L D V f241 r a s env d _ (NMV_240.cut a s env)` | `NMV_240.root` |
| `NMV_Roots.r344` | NMV_ | `NMV_344.root` (from `NMV_RslFold.fold344` + native cut) | `NMV_344.root` |
| `NMV_Roots.g2` | NMV_ (G2) | `NMV_G2.frame` | `NMV_G2.frame` |
| `NMW_Roots.r221` / `.r213` | **unowned** (gap W-RSL) | `NMW_RSL.fold221`, `NMW_RSL.fold213` | `⟨NMW_RSL.fold221, NMW_RSL.fold213⟩` |
| `NMT_Roots.r094/.r328/.r345` | NMT_ | `NMT_094.fold`, `NMT_328.fold`, `NMT_345.fold` | `⟨NMT_094.fold, NMT_328.fold, NMT_345.fold⟩` |
| `NMP_Roots.r137/.r087` | NMP_ | `NMP_137.fold`, `NMP_087.fold` | `⟨NMP_137.fold, NMP_087.fold⟩` |
| `NMO_Root.r136` | NMO_ | `NMO_136.root` | `⟨NMO_136.root⟩` |
| `NMN_Root.r064` | NMN_ candidate / NMQ_ credit | `NMN_064.rslRefines` (NMN_064.root through the RSL byte carrier) | `⟨NMN_064.rslRefines⟩` |
| `NNC_G1a.{w,weak,writeFree,okHeader}` | NNC_ | `NNC_G1a.law`, `.weak`, `.writeFree`, `.okHeader` | `⟨NNC_G1a.law, NNC_G1a.weak, NNC_G1a.writeFree, NNC_G1a.okHeader⟩` |
| `NNC_NMFPrime.{Ev,root0_or_event}` | NNC_ (G1c) | `NNC_NMFPrime.event`, `NNC_NMFPrime.root0_or_event` | `⟨NNC_NMFPrime.event, NNC_NMFPrime.root0_or_event⟩` |
| `NNC_CaseSplit.event_eq` | NNC_ | `NNC_CaseSplit.event_eq` (expected `fun _ h => h`, by `rfl` on the event term) | `⟨NNC_CaseSplit.event_eq⟩` |
| `NNC_R0Rep.rep` | NNC_ | `NNC_R0Rep.rep` (snapshot law TX2:239 + `V0.Root0 = NLP_InputDomain.Root0` on bytes) | `⟨NNC_R0Rep.rep⟩` |
| `NND_A1.stage1` | NND_ | `NND_A1.stage1_ret` (from the per-definition equalities 345/328/094=op10) | `⟨NND_A1.stage1_ret⟩` |
| `NND_A2.stage2` | NND_ | `NND_A2.stage2_ret` (241/242/233/234, tx2auth=op11, decoder slots) | `⟨NND_A2.stage2_ret⟩` |
| `Sig.Exhibited` | NND_ | `NND_Missing.instance` | ctx built with `missing := NND_Missing.instance …`; `hx := rfl` |
| `NNE_A3.accepted1` | NNE_ | `NNE_A3.accepted1` | `⟨NNE_A3.accepted1⟩` |
| `NNE_A4.accepted2` | NNE_ | `NNE_A4.accepted2` | `⟨NNE_A4.accepted2⟩` |
| `NNE_A5.recorded` | NNE_ | `NNE_A5.recorded` | `⟨NNE_A5.recorded⟩` |
| `NNE_EntryRep.route1/2` | NNE_ | `NNE_EntryRep.route1/2` | `⟨NNE_EntryRep.route1, NNE_EntryRep.route2⟩` |
| `Sig.args*/state*/env*/Out*/EnvRep/TraceRep` | NNE_ (definitions) | `NNE_Rep.*` | fields of the host `Sig` instance |

### Premises of `top` that are not interface fields

| Premise | Classification |
|---|---|
| `c : S.Ctx` | the headline binders, unchanged; every approved trust row inside them stays a hypothesis |
| `hx : S.Exhibited c` | substitution of `missing` (ruling (s)); `rfl` at the host |
| `queries` | L154 statement parameter, unchanged |
| `frame : S.GameFrame c` | game (a)(b)(c) plus `copied`/`actions`: content of the headline's `game` binder, retained as before; no job here discharges it (runtime and Stream C) |
| `trace : S.TraceRep c I.entry` | physical trace association of game (d) (narrowed D188): the same content the headline's `game.recorded` asserted, now stated over the actual entry |
| `ok1`, `ok2` | the actual TX1/TX2 entry runs returned Ok: the antecedent of soundness, replacing the model-form `accepted1/2` |
| `out1`, `out2` | `saved/post1/final1/post2/final2` are the carrier images of the actual outputs (a choice of the headline's free output binders) |

## 4. Gaps and mismatches that matter

1. **W-RSL (unowned).** No live job owns the RSL-form, library-parametric folds for 221/333 and 213/330. NMW_ (merged) proved `process_fold`/`entry_fold` over `NMW_RowSpecs.RowSpec` (`native args before = model args before`, on the Aeneas carrier with a `secondDomain` parameter), not over `RSL.TX2_221.Ref`/`TX2_213.Ref`. The lead's G1b amendment went only to NMS_ and NMV_. TCK listed NMW_ as well. Needed: `NMW_RSL.fold221 : ∀ V, RowSpec_344 → RowSpec_240 V → RowSpec_221 V` and `fold213`, each with its native cut.
2. **ALLOC.** `Accepted1/2` mention `state1/final1/state2/final2`, the `Allocator A` item's reserve and cleanup. RSL drops allocator internals (ruling (bl)(3): `Spec.alloc` carries no state). NNE_ already records this (NNE_HANDOFF: "never inferred from an allocator-erasing RowSpec alone"). In TAS it sits inside A3/A4 through `Out1/Out2`. If it cannot be proved from the `allocator` binder and the D189 wrapper definitions, it needs an owner decision. It must not be added as trust silently.
3. **G2 write-freeness.** `NMV_Roots.g2` holds only if G1a's `w` and the `PoolLib` Spec fields (`encodeStatement`, `emitResult`) emit no `Event.write`. TAS therefore asks NNC_ for `NNC_G1a.writeFree`. Neither brief asks for it.
4. **A5 via NMW route folds.** The stage2 arm of `NMW_Fold.entry_fold` needs `RowSpec_240 native.second model.second secondDomain`, that is native = model. Off Root0 that equation is unsupported (TCK 2.3), so it cannot cover non-selected ASQ8 invocations. A5's ASQ8 arm must come from G2 alone (store unchanged, `.rollback`), which is what `NNE_A5.recorded` takes.
5. **A1/A2 direction and environment.** The RSL Ref is a relation over a quantified `Env` with allocation-abort nondeterminism, while the AdapterRw model is a function over `sdk c` ops. TAS needs the returned-arm direction at an `Env` satisfying `EnvRep` (sha256 via `syscall`/`p1`, PDA replies, clock = slot). NND_ also reports that the AdapterRw emission parent is 81521c77, not frozen 4bb3b3f.
6. **Statement shape.** `top` concludes `Bound ∧ (Concl ∨ Event)`. In the event branch the full headline conclusion is not available, because `accepted2` at the model is unsupported off Root0. The failureModel bound is still obtained Root0-free from `FJp_Residual.numeric`, which takes no accepted/game/admission binder. `Event` is the headline's own charged alternative, so no metric changes. The lead should confirm this is the intended top statement.
7. **Representation predicates.** `args*/state*/env*/Out*/EnvRep/TraceRep` are host definitions, and the latter three appear as `top` premises. A vacuous definition would make `top` vacuous. The host must define them as concrete equalities and exhibit a satisfying ctx for any actual run (checklist item 8).

## 5. Final host assembly checklist (for the Codex job)

1. Workspace: the coherent host workspace with the latest ledger export plus NLX_COMBINED_IMPORT. Add RSL_, TCK_WeakRoot0, TAS_Interfaces, TAS_Top and every job module at its pinned commit. Use one capped scope (6G/8G/swap0; one optional 16 GiB aggregation scope, as TCK sized it).
2. Fix `V0` as the canonical library: `Root0 := fun ck pr => NLP_InputDomain.Root0 <ck> <pr>` on byte carriers, `tx2auth :=` the NMN_064 law, `VErr :=` verifier::Error. Fix `L`, `D`, `VL`, `P`, `C` as the CLOSED instantiations named in RSL_INDEX.md. Check each against the CLOSED statement ((bm)(2)(c)).
3. Fix `I : Impl L V0 VL` as the actual observed-semantics functions. Coherence check: every job's root must name the SAME constant for the same function. Check each with `example : <job root type> = <TAS field type> := rfl`, and record any representation difference as a finding.
4. Define the host `Ctx` structure (headline binders) and `S_host : Sig`. Prove `env1_rep`, `env2_rep` and `mkGame`, which should be constructors or `rfl`.
5. Instantiate every interface structure using the table in section 3. Build `A0_Digest` by `rfl` for stage1/stage2 plus `digestSource` under `Exhibited`.
6. State `AspisR1.TAS_Final.deployed_actual` by applying `RSL.TAS.top S_host L D V0 VL P C I …`, then `simp only` / `show` to unfold the `Sig` fields so the conclusion reads with the real headline terms.
7. Statement audit, before/after. Compared with `deployed`, removed: `native1`, `native2`, `extraction`, `accepted1`, `accepted2`, `game`. Added: `ok1`, `ok2`, `out1`, `out2`, `frame`, `trace`, `hx`. Confirm there is no Root0 hypothesis, no hash-injectivity, no new trust row, and that `queries` is unchanged.
8. Non-vacuity: construct, for an arbitrary actual run, a ctx satisfying `Out1/Out2` (outputs defined as carrier images) and show `TraceRep`/`GameFrame` are the recorded-trace facts, not `False`.
9. Audit: `#print axioms` on the final theorem (standard only); raw ax2 walk of the final root; record target, exit, wall, peak RSS, swap, revision and axioms (AGENTS.md section 6).
10. Ledger: record G0 as described in TAS_LEDGER_NOTES.md. No row credit comes from G0 itself.
