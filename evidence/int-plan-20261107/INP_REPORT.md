# INP: what the split-B top still needs from integration, and the cheapest sound route

Target not yet established. This package closes no row, discharges no premise and adds no trust. It is a read-only diagnosis of the seven items NNH_ run 4 left open (NNH_HANDOFF.md, NNH_REMAINING.md, NNH_CONTINUATION_STATUS.json, NNH_G0_MISSING.json at research dd650585170), checked against the TAS/TFM/EVB/AMN material and the merged modules they name. No Lean was compiled here; every classification below rests on definitions quoted from research, and each one that still needs a check is listed as a preflight item in section 4.

## 0. Why the run bled tokens

Four causes recur in the handoff. They matter because the plan in section 4 is built to avoid them.

1. **Conditional consumers were rebuilt five times.** NNH_G0Partial, G0Libraries, G0Candidates, G0With064 and G0WithG1a each re-state the whole split-B top over an arbitrary `Sbase : Sig`, each with its own raw audit. Every one of them still takes `sp hl a0 R rs hb nmfB r0 a1 a2 X` as arguments. A theorem over an arbitrary Sig can never discharge A1, A2, NMF_B or ExecB, because those are facts about the concrete headline binders, so none of these generations moved a field. The literal host Sig was never built, although TAS_WIRING §5 step 4 put it first.
2. **Whole-object shapes were tried before pointwise ones.** These are L454 (dictionary-wide currentBase erasure), L559 (whole-source congruence, heartbeat limit) and L570 (rfl-first dispatch). Each was retired only after it failed.
3. **The rev2 to rev3 rebuild took 116 scopes.** It was mandatory, but rev4 (ruling (bs), merged 521d37fa6ed) has since changed RSL_TX1_094/328/345 again, and the NNH TX1 chain was built at rev3.
4. **Waiting was mixed up with proving.** The handoff lists row candidates (094/328/345, 233/242/241) as waits next to A1/A2. A1/A2 do not mention `I` at all (AMN §2.1). Only the final instantiation waits for rows.

## 1. Item by item: what the top consumes, and the verdict

The top is `RSL.TASB.top_splitB` (evidence/top-assembly-20261107/TAS_TopB.lean). NNH's latest consumer instantiates it as `AspisR1.NNH_G0WithG1a.deployed_splitB_conditional`, which takes as arguments `Sbase runtime d r I0 allocation217 alloc1 alloc2 sp hl a0 registry nmx nms nmt nmp R rs hb nmfB r0 a1 a2 X fx w H queries run`.

### 1.1 A2: the SDK op11 query/Merkle/finish continuation. Verdict: (a) required, Ok direction only, and not supplied by the TX2:065/064 roots

The consumed field (TAS_Interfaces.lean):

```lean
structure NND_A2 where
  stage2 : ∀ c a env o r, S.Exhibited c → S.EnvRep c env →
    TX2_241.Ref L D V0 a env o → o.exit = .ret r → S.ModelRet2 c a r
```

At NNE's physical Sig, ModelRet2 begins `a = child2 … → r = .ok () → …` (AMN §1.5), so only the selected Ok arm is consumed. NNH has reduced the actual SDK stage2 to the op11 call (`NNH_Stage2To064.source`, L667). The exact open target is `NNH_ExactRemainingTypes.tx2Op11`:

```lean
def tx2Op11 : Prop := ∀ missing env err reserve, NJC_FilledClause.reserved reserve = env.reservation →
 ∀ pub proof ck, RSL.TX2_241.Dom064 V0 (bytes pub, bytes proof, bytes ck) →
 LIBB_Tx2EnvCode.code env pub proof ck = .ok (.Ok ()) →
 (NNH_CorrectConfiguration.sdk missing env err reserve).op11
   (SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk missing env err reserve))
   pub proof ck () none = .ok (.Ok ())
```

**Check 2a: do the CLOSED TX2:065 root (`NLT_CompleteRoot.root`) and the TX2:064 root (`NMN_064.root`) already cover this, so that A2 needs only an instantiation? No.** Those two roots point the other way. `NLT_CompleteRoot.root` concludes `RowSpec H d pub proof ck hash`. Its resolved arm says that the native result equals the canonical source run:

```lean
def ResolvedLaw … := let f := NLT_FrameFromCuts.frame records
 result = NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish) d pub proof ck hash none ∧ …
```

`NMN_064.RowSpec` wraps that in the parser (`Native H s outcome events → Law H s.args outcome ∧ events = chronology …`). Both are **actual → canonical** (`NJJ_Common.run`), and the top already consumes them as `NMN_Root.r064` and G1a (installed: `NNH_064Install.root`, `NNH_G1aEnv.field`). A2's op11 obligation is **canonical → model**. `LIBB_Tx2EnvCode.code` is `parse; NJJ_Common.run r r (NLP_NativeMerkle.action (H env)) (NLB_Parent.finish r) (digest env) …`, while the model slot is a different term:

```lean
-- lean/Tx2I_Install.lean
def install adapter base finish : AdapterRw.Ops :=
  {adapter with op11 := VTop_Stages.verifier.candidate.tx2_authenticated (stage base finish)}
-- lean/DrvC_Installation.lean: sdk c = … (Tx2I_Install.install c.adapter
--   (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase) c.reserved c.query c.geometry)) c.finish) …
```

No CLOSED root states anything about `tx2_authenticated (stage …)` at the filled configuration in the canonical-to-model direction. The obligation is therefore real. It is much smaller than the handoff suggests, because closed material already fixes most of its shape:

- `Dom064 V0` contains `V0.Root0` (RSL_TX2_241.lean: `… ∧ V.Root0 x.2.2 x.2.1`), so op11 is needed only under Root0 and the three extents. A4, and hence A2, is used only on the Root0 branch of the top (TAS_WIRING §1 step 5).
- `NHT_Tx2CommonModel.source` (tx2-model2-20261106) proves by `rfl` that the NHT emitted common body equals `verifier.candidate.tx2_common (constants ops)`. `NJJ_Common.run` is "a mechanical substitution in the pinned NHT emitted common body", and `NNH_Tx2SourceConfiguration.stage` already installs `NHT_Tx2CommonModel.constants`, `op2 := NJC_ClosedCalls.inactive` and `op13 := NHV_ReleaseOps.mark`.
- `Tx2N_Execution.common` (lean/) is the step decomposition of model `tx2_common (control …) = ok (.Ok ())` into reader, powers, geometry, pending, query, flush and finish, with the exact slot terms: pending `Port3_NativePendingInstall.source reserved` (the same term as `NJJ_Common.pending`), geometry `Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometry)`, query `Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query))`, and merkle through `Op5T_Concrete.stage_source` (= `Port4B_Install.batch`). The A2 continuation is the converse composition along the same steps: every canonical step returned Ok, and each model slot equals the canonical call at those arguments.
- The slot equalities still open are pointwise. They are: geometry (`NJC_ClosedCalls.geometry` against the model geometry at `NFN_NEW_GeometryDictionary.adopted`; NJC_ClosedCalls already has the `literal`/`cohort` pair), query (`NHT_PacketOps.query NJJ_QueryOps.concrete 0 0` against Port3 query at `query := NJJ_QueryOps.concrete`), merkle (`NLP_NativeMerkle.action (H env)` against `Port4B_Install.batch` at the env digest; `NLB_CommonTransport.common_transport` is the reply-congruence pattern), and finish (`NLB_Parent.finish r` against `Port4D_FinishInstall.finish (IDa_Deployed.finish reservation)`). The resume prefix is done (L627/L699/L700).

### 1.2 A1: op10/op21/op24 body transport. Verdict: Ok arm (a) required; Err arm over-asked in form (b); it does not wait for TX1:094

```lean
structure NND_A1 where
  stage1 : ∀ c a env o r, S.Exhibited c → S.EnvRep c env →
    TX1_345.Ref VL P C a env o → o.exit = .ret r → S.ModelRet1 c a r
```

The exact targets are `NNH_ExactRemainingTypes.tx1Ok` (Returns value `Ok b` gives `stage1_owned (sdk …) … = .ok (.Ok saved)` with `bytes saved.deref = b`) and `tx1Err` (Returns `.error e` gives `∃ pe, stage1_owned … = .ok (.Err pe)`). op10 is installed, not free: `AspisS6CurrentFirstInstallation.install ops vops := AspisS6CurrentCodecInstallation.install {ops with op10 := current vops}`. So op10 is the TX1 current-verifier body over the model dictionary, and op21/op24 are codec slots of the same installer.

- **Ok arm: required.** native1 is inspected by game (d) at every stage1-route invocation (`firstEffect … | .ok (.Ok (saved,_,_)) => commit …`), and by A3 for `accepted1` (AMN §1.2).
- **Err arm: over-asked in form.** `firstEffect`'s other arm is `| _ => (store,.rollback,.inl reply)`, so game (d) needs only that the model reply is not `.ok (.Ok _)` when the canonical value is an Err. `issued` likewise matches `| _ => []`. The present form `∃ pe, … = .ok (.Err pe)` additionally forces model liveness on every Err path, which is the "decoder liveness" in NNH_REMAINING. AMN §1.2 already showed that a model `fail` also rolls back. The cheaper route restates ModelRet1's Err clause as `¬ ∃ x, model1 … = .ok (.Ok x)` in an NNH_-prefixed copy of NNE_AcceptanceSig.physical, and adapts the one consuming lemma (NNE_Stage1Error) under an NNH_ name. The top statement is unchanged. This weakens an intermediate deliverable, as in AMN §4, and the lead records it.
- **Check 2b: will the TX1:094 row root supply op10 once NNG_ closes it? No. A1 should not wait for it.** `NMT_Roots.r094 : RowSpec_087 VL P I.f087 → RowSpec_094 VL P I.f094` is about the actual `I.f094` lying in the reference (actual → canonical). The top consumes it separately through `nmt`. A1 is canonical (Returns value) → model op10. Even if the emitted frozen tx1 body and the model's `current vops` were the same Lean term, row membership plus returned-determinism would still leave model liveness open (AMN `alloc_admits_both`). A1 uses only the RSL Ref (frozen at rev4) and the delivered canonical libraries VL/P/C, so it can proceed now.
- **Rev4 dependency.** Ruling (bs) added P1880 to RowSpec_094's and RowSpec_328's Domain and `P1880Discharge` to 345. `Ref` is unchanged (RSL_REVISION4.md), so the NNH Returns evaluator `NNH_ReturnsBundle.tx1Value` should carry over, but the TX1 chain was compiled at rev3 and must be recompiled at rev4 before any A1 claim. That is one focused rebuild, not a redesign.

### 1.3 Literal-host NMF_B. Verdict: (a) required; its core is already supplied (c); only cut production remains

```lean
structure NNC_NMFPrimeB (g) (R) where
  root0_or_rec : ∀ c, S.Exhibited c → (weak entry Ref for every invocation) →
    (actual TX2 entry Ok) → S.Accepted1 c (S.model1 c) → S.Game c … → S.Extraction c … →
    S.Queries c … → R.SelectsPair c → S.Root0Native c ∨ R.EventRec c
```

The following are merged and standard-axiom:

- `AspisR1.NNC_NMFB.root0_or_rec` (root0-weak-20261111). Its conclusion is `Root0 s.checkpoint s.proof ∧ RowSpec … ∨ BinRawByteCollisionTargets.event … (Q+2965) (eval H (Hiq_RecordedJoint.program (ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) Q) ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)))`, which is literally E_rec.
- `AspisR1.NNC_ActualRoot.actual`, the same theorem at the adaptive entries `NNC_ActualChoices.first a H` / `second a H …`, with Realizes by `rfl`.
- `NNC_RecSelect.selects` (the EVB RecSelect host theorem) and `NNH_StateSelect` (its a⊤ specialisation).
- `NNH_NMFPrime.assemble`, which builds the exact TAS field from `selected` (produce a `Packet`), `rootImage` and `eventImage`.
- The native half of the Packet (`d hash world domain oracle records events native`), from `NNH_EnvEntryWorld.native` (L486), `NNH_WeakEntryNative.produce` (L263) and `NNH_G1aEnv.field` (L467).

**The genuinely open part is cut production**, which consists of the Packet fields `f s cuts origin writerRoot persisted writerHeader`. NNC_ActualRoot's docstring says "the cut-production obligation remains explicit". `NMF_GameRoot` obtains these fields only by destructuring `RPx_Deployed.deployed`, which needs `accepted2`, so it cannot be reused on the event branch. A Root0-free source is needed for each field:

- `f`, `writerRoot` and `writerHeader`: TX1 only, from `Accepted1` at the model. `ARU_FirstHeader.accepted` (lean/, already in the ledger27 root list) gives the writer header from `first_decoded … = ok (.Ok saved)` alone. `ARU_WriterReached.reached` and `NMF_WriterRoots.serialized` give the writer root shape.
- `s`, `origin` and the TX2 half of `cuts`: the SAME native records (`NNH_Tx2ConcreteInputs.produce` L629 preserves the actual index0/index6 slices and the 1880-byte statement) identified with the model's account reads of `e2.second secondSizes`.
- `persisted`: `game.checkpoint` key equality, `p.copied t = saved` (GameFrame) and RuntimePersistence.

`Associated`, `rootImage` (with `Root0Native c := ∃ s, <cut> ∧ Root0 …`) and `eventImage` are host definitions, closed by `rfl`/`Iff.rfl` once the Packet's `source` is the RecordedCharge source (section 1.7). No `selected`, `rootImage` or `eventImage` hypothesis may appear in the final theorem.

### 1.4 RZ-STATE ExecB. Verdict: (a) required, but definitional once the host Ctx exists

`RSL.TASB.ExecB` has fields `Fixed World Oracle In1 In2 first second build realizes_mk exhibited_mk QueriesF queries_mk ERec eventRec_mk`. Its docstring gives the host term of each: `build` is the Ctx constructor; `exhibited_mk` is `rfl`; `queries_mk` is `id`; `eventRec_mk` is `Iff.rfl`. Under the owner's RZ-STATE decision, `first fx H := (eval H (normalize a).first).2`, and `realizes_mk` is the eval-of-map lemma that NNH_StateNormalize already proves (L033/034). Nothing here is mathematical. It is blocked only by the absence of a concrete `Ctx`, which is cause 1 of section 0. The conditional theorem's "arbitrary X" must be replaced by this one literal instance; the arbitrary X is not RZ-STATE installation.

### 1.5 All-H deployed averaging. Verdict: (b) over-asked in form; a "joint view that determines World" is not well posed

`TASB.deployed_charge` is proved at stand-in level for any `Ex : Expect X.Oracle` (an expectation on every function `Oracle → Rat`) and any `wOf : Oracle → World`. NNH's blocker reads: "World includes physical p/t/u/actions and saved/post states; no actual joint program/view determines them yet". Because `wOf` is arbitrary (the owner's condition (1): binders may depend on H arbitrarily), no program's view can determine `wOf H`. Requiring one would restrict the world, and that restriction must not be added. The host expectation `lazyMean J emptyTable` is defined only on functions of J's view, so `TASB.Expect` cannot be instantiated with it on the fail indicator.

The sound form avoids that instantiation. The deployed per-attempt failure is dominated pointwise, for every `wOf` and every `H`, by a view-measurable function whose expectation the existing chain already bounds:

```
deployed_outer : ∀ wOf H, max (r H) (ind (Runs … (ctxB X fx (wOf H) H) ∧ ¬ OutcomeRec …)) ≤ m H + ind (E_rec H)
```

This follows from the compiled `RSL.EVB.no_second_charge` plus `TASB.fail_sub_rec`. Combined with `NNH_RecordedCharge.bound` (`lazyMean (recorder … (normalize a) Q) … ≤ accountLoss Q`) and the existing `failureModel ≤ total (Q0+Q1)` chain at `a := normalize a`, it gives outer probability ≤ total(Q0+Q1). The adversary stays universally quantified, there is no conditioning on Realizes and no H is excluded, and E_rec is charged once. This is an interpretation of owner condition (5) ("the final averaging theorem compiles"), not a contract change: the number, range, metric and adversary are unchanged. The lead should record it, and tell the owner it is the only form that keeps `wOf` unrestricted.

### 1.6 "Host/Missing/World installation". Verdict: Ctx and Missing (a) required but definitional; World (b) needs no physical construction

**Which headline binders.** TAS `Sig.Ctx` is the binder block of `RPx_Deployed.deployed` minus `native1 native2 extraction accepted1 accepted2 game`: `L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 missing indexError reservation hashv sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2 saved post1 post2 root length prior words p t u actions RuntimePersistence D a Q0 Q1`. "Missing" is the binder `missing : IDa_Deployed.Uninstalled CoreError`:

```lean
structure Uninstalled (CoreError : Type) where
  adapter : AdapterRw.Ops; currentBase : AspisR1CurrentCaller.Ops; stageBase : VTop_Stages.Ops
  reserved : Bool; query : Port3_NativeQueryBody.Ops; geometry : Port3_NativeGeometryBody.Ops CoreError
```

and `Exhibited c := c.missing = <instance>`, a substitution of a universally quantified binder (ruling (s); TAS `Sig.Exhibited` docstring). "World" is `ExecB.World`, the per-world remainder `saved post1 final1 post2 final2 p t u actions RuntimePersistence` (TASB docstring), with the allocator states fixed to `true` by ruling (bo).

**Is there a canonical existing instance? Not a complete one, but the right shape exists.** `NND_Missing.instance`, which the TAS table names, was never delivered. `NND_MissingPartial.select` installs decoder slots only, and its docstring says it "does not claim to supply TAS.Exhibited". It is also not the configuration the NNH transports are stated over. The de facto canonical instance is NNH's:

```lean
NNH_CorrectConfiguration.residual missing env := NNH_Tx2SourceConfiguration.fill
  {missing with adapter := NNH_AdapterStdCorrect.install {missing.adapter with op19 := .ok 1520#usize, op44 := NNH_RuntimeErrorValue.error}} env
NNH_Tx2Configuration.select missing env := {missing with adapter := NNH_Tx2ModelSlots.install missing.adapter env, reserved := env.reservation}
```

`tx1Ok`, `tx1Err` and `tx2Op11` all quantify over every base `missing`, so the slots they leave untouched are irrelevant. The literal instance is therefore `missingLit c := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 (envOf c)) (envOf c)` for any fixed inhabitant `m0`, with `CoreError := NFN_NEW_GeometryDictionary.CE` and `envOf c := NNH_HostEnv.environment (sha c) (pda c) (clock c) (reservation c)`.

There is a useful simplification. `NNH_HostEnv.install` already sets `env1 = env2`, and `EnvRep` pins all four Env components (`env.sha256 = sha ∧ env.pda = pda ∧ env.clock = clock ∧ (env.reservation = true ↔ reservation = .Ok ())`). If `RSL.Env` has exactly these four fields (preflight P1), then `EnvRep c env → env = envOf c`, and A1/A2's `∀ env, EnvRep c env` collapses to the single env that `missingLit` uses. Ruling (s)'s per-slot representability and call-site obligations are subsumed in the TAS route: the extraction binder is taken at `native := model` (A0, by `rfl`), and the actual code meets the model only through the RSL rows plus A1/A2. The one slot fact A0 still needs is `digestSource`, the model op43 against the headline `hashv` (preflight P2).

**World** needs no installation. The theorem quantifies over every `w` (and every `wOf`), so `World` is just the Σ-type of those binders, and the physical association stays in `Runs.frame/trace`, which are the headline's own retained hypotheses (ruling (ao)). The averaging concern is settled by section 1.5.

### 1.7 "Same-recorder failure inclusion". Verdict: (c) already supplied

`TASB.fail_sub_rec` (compiled) is exactly the inclusion "a successful actual run whose Outcome(bad := E_rec) fails lies in E_rec at the SAME H". It is a corollary of `top_splitB`, so it needs no proof of its own once the fields exist. "SAME recorder" then reduces to one definitional check. NNC_NMFB's event, at `allocator := NNE_AbortIndicator.allocator`, `a := NNH_StateNormalize.normalize a` and `Q := Q0+Q1`, must be syntactically `NNH_RecordedCharge.recorder copy base err r hashv a (Q0+Q1)` (both are `Hiq_RecordedJoint.program (ARX_LocalCharge.bounded (ART_PartialAccount.account (FIp_Install.configuration err base r) hashv copy NNE_AbortIndicator.allocator CPH_Program.verifier (normalize a)) Q) ARQ_Observer.project (ARQ_Observer.select …)`), and `ExecB.ERec fx H` is defined as that event. This is one `rfl` lemma. No separate inclusion theorem is required.

### 1.8 Items the user list does not name but G0 still needs

- `rs : RecSelect` (c): supplied by `NNC_RecSelect.selects` + `NNH_StateSelect`, instantiated at the host.
- `hb : HeadlineB` (a): `outcomeRec`, which is Outcome with inner `bad := E_rec` (owner condition (3)). EVB §2.3 sizes it as `FJv_DRelease.remove'` plus a `FJv_DNativeAccepted` copy, about 200 lines with heavy imports. No delivered module yet.
- `sp, hl, a0, r0` (a), host assembly: `Split` and `Headline` are reassociation and `RPx_Deployed.deployed`/`FJp_Residual.numeric` at the host; `A0` is `⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, digestSource⟩`; `R0Rep` comes from NNC_ByteCarriers/SnapshotRep.
- Ledger27 change, no wait: TX1:137/087 and TX2:217/234 are now CLOSED (`NNG_Candidate137.candidate`, `NNG_Candidate087.candidate`, `NMX_R3_RegistryRoot.root` and the 217 root in NNK_AUDIT_ROOTS.json). The G0 should consume these CLOSED roots instead of the candidate producers in `NNH_LeafInstall`/`G0Candidates`.

## 2. Summary table

| Item | Verdict | What remains |
|---|---|---|
| A2 op11 continuation | (a) required, Ok only, under Root0 | pointwise slots geometry/query/merkle/finish plus converse composition along `Tx2N_Execution.common`; then `AMN.viaReturns2` |
| A1 op10/op21/op24 | Ok (a); Err over-asked (b) | op10 current-body transport, codec ports into stage1, 328/345 glue at rev4; Err as `¬∃x, = ok (.Ok x)` |
| Literal NMF_B | (a), core supplied (c) | cut production `f s cuts origin writerRoot persisted writerHeader`, Root0-free |
| RZ-STATE ExecB | (a), definitional | literal ExecB once Ctx exists |
| All-H averaging | (b) over-asked form | `deployed_outer` pointwise domination plus existing bounds; lead records the reading of condition (5) |
| Host/Missing/World | Ctx/Missing (a) definitional; World (b) | `HostCtx`, `missingLit`, `envOf`; World is a Σ-type |
| Same-recorder inclusion | (c) supplied | `TASB.fail_sub_rec` plus one `rfl` |

## 3. What waits for row candidates

Only the final instantiation waits. The fields `nmx` (233), `nms` (242/241) and `nmt` (094/328/345) of `top_splitB` require the row roots, and `nmw`/`nmv` stay instantiated generically. A1, A2, NMF_B, ExecB, HeadlineB, the host Sig, the averaging and the ledger27 switch-over all take row facts as hypotheses of their own statements (NMF_B takes the weak entry Ref as an argument), or do not mention `I` at all. They can be built now.

## 4. Minimal ordered plan for a fresh integration run

The binding rules are these. Build one literal host and one final consumer. Do not create another conditional G0 generation. Use pointwise slot lemmas only, never whole-dictionary or whole-function congruence. Each step has a scope cap; at the cap, stop that step and report the exact slot. The scope estimates are realistic ranges and allow for one failed shape per step.

| Step | Content | Scopes | Waits on rows |
|---|---|---|---|
| S0 | Compile `NNH_ContinuationCombined` with `NNH_Stage1ZeroCurrent`; keep `NNH_Stage1ZeroOk` and `NNH_U64Bytes` out of every import | 1–2 | no |
| S1 | Preflight, all cheap: P1 `RSL.Env` has exactly sha256/pda/clock/reservation, so `EnvRep c env → env = envOf c`; P2 A0 `digestSource` holds at `op43 := LIB_Env.hashv (envOf c)` against the headline `hashv`/`syscall`; P3 slot table for op11 (which of geometry/query/merkle/finish are `rfl` at the filled configuration); P4 NNC_NMFB event `=` RecordedCharge recorder by `rfl`; P5 rev4 recompile of the NNH TX1 Returns chain | 6–10 | no |
| S2 | Literal host: `HostCtx` structure, `missingLit`, `S_host : Sig` (on NNH_HostEnv.install), NNE `Data`/`RecordSig.Data`, `ExecB` literal (RZ-STATE), `Split`, `Headline`, `A0`, `R0Rep`, RecSig, and RecSelect from `NNC_RecSelect.selects` | 10–16 | no |
| S3 | A2: `tx2Op11` by pointwise slots and converse composition; compose `Stage2To064` + op44/op53 tail + 241 Returns via `AMN.viaReturns2` → `NND_A2 S_host` | 10–18 | no |
| S4 | A1: rev4 base; op21/op24 codec ports into stage1; op10 current-body transport; 328/345 glue; Err in `¬∃x` form with NNH_ copies of the physical Sig clause and NNE_Stage1Error → `NND_A1 S_host` | 30–55 | no |
| S5 | NMF_B: cut-production packet (TX1 from ARU_FirstHeader/WriterReached; TX2 from the SAME native records; persisted from game + RuntimePersistence); `NNH_NMFPrime.assemble` at the host | 15–30 | no |
| S6 | HeadlineB `outcomeRec` (remove′ plus DNativeAccepted′) on the build host under caps | 6–12 | no |
| S7 | `deployed_outer` averaging plus the same-recorder `rfl` | 2–4 | no |
| S8 | Final G0: one consumer at `S_host`, ledger27 CLOSED roots for 137/087/217/234, row roots for 094/328/345 and 233/242/241; the reserved 16 GiB scope; one raw axiom audit; non-vacuity (TAS §5 step 8); one manifest replay | 5–10 | **yes**: TX1:094/328/345 (NNG_) and TX2:233/242/241 |

The total is about 85–155 scopes before S8, and roughly 0.5–1.0M tokens if each step starts from its own short brief rather than from the accumulated handoff. S3, S4 and S5 are independent after S2 and can run as parallel jobs. S4 is the largest and most uncertain step, because op10 is the full TX1 verifier body.

## 5. Escalations and records

- Lead to record: the A1 Err arm restated as `¬∃x, model1 … = .ok (.Ok x)` (weakens an intermediate deliverable; top unchanged).
- Lead to record and report to the owner: the reading of condition (5) as pointwise domination with `wOf` unrestricted (section 1.5). A literal single `lazyMean` of the fail indicator would require restricting World and is not recommended.
- No trust row, metric, frozen source or RSL change is proposed.

Target not yet established.
