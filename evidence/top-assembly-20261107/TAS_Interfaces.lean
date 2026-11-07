/-
TAS_Interfaces: the top-assembly (G0) interface package.

Target not yet established.  This module proves no row and discharges no
premise.  It fixes, as Lean types, EXACTLY the statement each live job must
hand over so that `TAS_Top.top` (the composition) goes through by
instantiation.  Core Lean plus RSL_ (evidence/rowspec-lead-20261107) and
TCK_WeakRoot0 (evidence/top-check-20261107) only.

Layout.
  * Section 1: `Sig`, the headline stand-ins.  The headline objects
    (Aeneas carriers, AdapterRw models, AspisR1.RPx_Deployed.deployed's binder
    block and conclusion) are not importable on a development machine.  Each
    is a FIELD of `Sig`, never an `opaque`/`axiom`, so the final host assembly
    instantiates `Sig` with the real headline terms and every TAS theorem
    specialises by application.  Each field's comment names the exact host
    term it stands for.  TAS_WIRING.md lists them.
  * Section 2: the verifier-library family `lib` (G1b) and the 064 refinement
    predicate `Refines064`.
  * Section 3: `Impl`, the observed semantics of the actual frozen functions
    (RSL's `impl` arguments), one per row.
  * Section 4: one structure per job deliverable.  Row roots are stated as
    folds "child RowSpecs -> parent RowSpec" in RSL form (a closed root `r`
    is supplied as `fun _ => r`).  The TX2 parents 241/240/221/213 are
    parametric in the library (G1b).
  * Section 5: small RSL lemmas the top uses (route inversion of the entry
    reference, the entry frame on ASQ8 data).

No sorry, no axiom, no Root0 hypothesis, no hash-injectivity premise.
-/
import TCK_WeakRoot0
set_option autoImplicit false

namespace RSL.TAS
open TX2_241 (V2Lib Dom064)
open TX1_345 (S1Lib)

/-! ## 1. Headline stand-ins -/

/-- Headline stand-ins.  `Ctx` is the headline binder block of
`AspisR1.RPx_Deployed.deployed` with the six binders this assembly supplies
removed (`native1`, `native2`, `extraction`, `accepted1`, `accepted2`,
`game`) and `queries` kept separate (it mentions `native1`).  It therefore
bundles, unchanged and still as hypotheses, `L sdk copy std allocator e1 e2
w1 w2 admission1 admission2 missing indexError reservation hashv sha256 H p1
syscall data1 data2 slot state1 state2 final1 final2 saved post1 post2 root
length prior words p t u actions RuntimePersistence D a Q0 Q1`. -/
structure Sig where
  /-- The binder block above (a host `structure` or Σ-type over those binders). -/
  Ctx : Type
  /-- `S2W_ExtractionBoundary.First`. -/
  First : Type
  /-- `S2W_ExtractionBoundary.Second`. -/
  Second : Type
  /-- `AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk c)`,
  `c := FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation`. -/
  model1 : Ctx → First
  /-- `AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk c)`. -/
  model2 : Ctx → Second
  /-- `ctx.missing` is the instance exhibited under ruling (s) by A2 (NND_), so
  that the decoder slots are the native decoders and `op43 = digest ctx.hashv`.
  At the host this is a SUBSTITUTION of the universally quantified binder
  `missing` (proved by `rfl`), not a hypothesis. -/
  Exhibited : Ctx → Prop
  /-- `S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv`. -/
  Extraction : Ctx → First → Second → Prop
  /-- `S2W_D189Wrappers.first n1 copy allocator e1 CPH_Program.verifier data1 state1 = ok (.Ok (saved,post1,final1))`. -/
  Accepted1 : Ctx → First → Prop
  /-- `S2W_D189Wrappers.second n2 allocator e2 CPH_Program.verifier data2 slot state2 = ok (.Ok (post2,final2))`. -/
  Accepted2 : Ctx → Second → Prop
  /-- Fields (a) consecutive, (b) checkpoint, (c) parent of
  `CPH_Game.DeployedPairExecution`, plus the two non-trace equalities of (d):
  `p.copied t = saved ∧ p.actions t = actions`. -/
  GameFrame : Ctx → Prop
  /-- (d), TX1 half: `CPG_RuntimeTrace.Executes n1 n2 copy allocator CPH_Program.verifier
  (CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 saved)
  actions (p.parentTentative t) (p.physicalEvents t)`. -/
  Recorded1 : Ctx → First → Second → Prop
  /-- (d), TX2 half: `CPG_RuntimeTrace.Executes n1 n2 copy allocator CPH_Program.verifier
  (cached (p.bank u)) (p.actions u) (p.parentTentative u) (p.physicalEvents u)`. -/
  Recorded2 : Ctx → First → Second → Prop
  /-- `CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator CPH_Program.verifier`. -/
  Game : Ctx → First → Second → Prop
  /-- The anonymous constructor of `DeployedPairExecution` (host: `fun _ _ _ f r1 r2 => ⟨f.a, f.b, f.c, ⟨⟨f.copied, f.actions, r1⟩, r2⟩⟩`). -/
  mkGame : ∀ c n1 n2, GameFrame c → Recorded1 c n1 n2 → Recorded2 c n1 n2 → Game c n1 n2
  /-- `∀ H, (ARW_Induced.issued n1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1` (L154, a statement parameter). -/
  Queries : Ctx → First → Prop
  /-- The eleven-conjunct conclusion of `AspisR1.RPx_Deployed.deployed` (with its `let`s unfolded). -/
  Concl : Ctx → First → Second → Prop
  /-- The three `failureModel` conjuncts of conjunct 5 of that conclusion:
  `failureModel runtime ≤ F3T_Numeric.total (Q0+Q1)`, the `maxQueries → ≤ (Q0+Q1+1)/2^100`
  clause and the `Q0+Q1=0` margin clause. -/
  Bound : Ctx → First → Second → Prop
  /-- The headline's charged event, verbatim from its `let` block:
  `BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
   (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P) F3X_Projection.project select))`
  with `P := ARW_Induced.program n1 copy allocator CPH_Program.verifier a` and
  `select := fun _ => P2P_NativeSelection.pair (sdk c) CPH_Program.verifier e1 e2 data2 slot`.
  It takes NO `Second` argument: that is the case-split independence. -/
  Event : Ctx → First → Prop
  /-- RSL image of the TX1 entry invocation (`e1`, `data1`): the instruction's
  program id, AccountInfo list (3 accounts, cells from `e1.heap.accounts`) and data. -/
  args1 : Ctx → TX2_240.Args
  /-- RSL image of the TX2 entry invocation (`e2`, `data2`), 7 accounts. -/
  args2 : Ctx → TX2_240.Args
  /-- RSL SdkState image of `e1.heap` (RSL_CHECK item 1: RSL SDK model = NLF_ model). -/
  state1 : Ctx → SdkState
  /-- RSL SdkState image of `e2.heap`. -/
  state2 : Ctx → SdkState
  /-- RSL oracle environment of TX1: `sha256` replies through `syscall`/`p1`, PDA replies
  of the runtime, `clock` unused. -/
  env1 : Ctx → Env
  /-- RSL oracle environment of TX2: as `env1`, with `clock := .ok slot` (RuntimeClockSlotBinding). -/
  env2 : Ctx → Env
  /-- `o` (an RSL observation of the TX1 entry) has carrier image `saved` (the written
  checkpoint bytes), `post1` (heap of the RSL post-state) and `final1` (allocator item). -/
  Out1 : Ctx → Obs (Except ProgramError Unit × SdkState) → Prop
  /-- As `Out1` for TX2: `post2`, `final2`. -/
  Out2 : Ctx → Obs (Except ProgramError Unit × SdkState) → Prop
  /-- `env` agrees with the ctx runtime oracles (sha256 via `syscall`, PDA, clock = slot). -/
  EnvRep : Ctx → Env → Prop
  env1_rep : ∀ c, EnvRep c (env1 c)
  env2_rep : ∀ c, EnvRep c (env2 c)
  /-- Physical trace association (game (d), D188 narrowed): every `.invoke` action of
  `p.actions t` / `p.actions u` was executed by the runtime as `entry` at the RSL images of
  its layout/store/data/slot, and every non-verifier action is the recorded Pool/runtime
  action (Stream C, NIB-P1..P4). -/
  TraceRep : Ctx → (TX2_213.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) → Prop
  /-- `∃ s, <native TX2 cut s at the selected occurrence (G1c)> ∧
  NLP_InputDomain.Root0 s.checkpoint s.proof`. -/
  Root0Native : Ctx → Prop
  /-- `NLW_ReaderHeader.decode ck = some (h pr, h pub)` where `h` is the SolanaDigest
  computed from `env.sha256` (transported to `H` by `p1`/`syscall`). -/
  readerHeader : Env → Bytes → Bytes → Bytes → Prop
  /-- `model1 c` applied to the carrier image of the TX1:345 arguments returns the
  carrier image of `r` (`native1 program accounts data = ok (enc r)`). -/
  ModelRet1 : Ctx → TX1_345.Args → Except ProgramError Bytes → Prop
  /-- `model2 c` applied to the carrier image of the TX2:241 arguments returns the
  carrier image of `r`. -/
  ModelRet2 : Ctx → TX2_241.Args → Except ProgramError Unit → Prop

/-! ## 2. The verifier-library family (G1b) -/

/-- Library with the canonical error carrier and printer of `V0`, and the given
Root0 predicate and TX2:064 law. -/
def lib (V0 : V2Lib) (R0 : Bytes → Bytes → Prop)
    (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) : V2Lib :=
  { V0 with Root0 := R0, tx2auth := w }

theorem lib_canonical (V0 : V2Lib) : lib V0 V0.Root0 V0.tx2auth = V0 := rfl

theorem lib_weak (V0 : V2Lib) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) :
    lib V0 (fun _ _ => True) w = TCK.weaken V0 w := rfl

/-- The actual TX2:064 observation lies in `w` on `Dom064 (lib V0 R0 w)` (the
G1b side condition: "V's tx2auth is refined by the actual 064 call on Dom064 V"). -/
def Refines064 (V0 : V2Lib) (f064 : Bytes → Bytes → Bytes → Env → Obs (Except V0.VErr Unit))
    (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) : Prop :=
  ∀ (x : Bytes × Bytes × Bytes) (env : Env), Dom064 (lib V0 R0 w) x →
    w x.1 x.2.1 x.2.2 env (f064 x.1 x.2.1 x.2.2 env)

/-- No account-data write event. -/
def WriteFree {α : Type} (m : Spec α) : Prop :=
  ∀ env o, m env o → ∀ c b, Event.write c b ∉ o.events

/-- Write frame of one entry-level observation: no write event, and every
returned post-state has the payloads of the pre-state. -/
def Frame (s : SdkState) (o : Obs (Except ProgramError Unit × SdkState)) : Prop :=
  (∀ c b, Event.write c b ∉ o.events) ∧
  (∀ r s', o.exit = .ret (r, s') → ∀ i, (s'.cells i).payload = (s.cells i).payload)

/-- ASQ8 instruction data (`Hiq_ReleaseRoute.asq8`). -/
def ASQ8 (data : Bytes) : Prop := data.take 4 = REQUEST_MAGIC

/-! ## 3. Observed semantics of the actual frozen functions -/

/-- RSL `impl` argument of every row, plus the actual TX2:064 call. -/
structure Impl (L : PoolLib) (V0 : V2Lib) (VL : VLib) where
  f217 : Bytes → Env → Obs (Except ProgramError LaneState)
  f234 : TX2_234.Args → Env → Obs (Except ProgramError Unit)
  f233 : TX2_233.Args → Env → Obs (Except ProgramError Authenticated)
  f242 : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L))
  /-- TX2:064 `tx2_authenticated(public, proof, checkpoint, SolanaDigest, None)`. -/
  f064 : Bytes → Bytes → Bytes → Env → Obs (Except V0.VErr Unit)
  f241 : TX2_241.Args → Env → Obs (Except ProgramError Unit)
  f240 : TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)
  f136 : TX1_136.Args VL → Observer → Env → Obs (Except VL.WErr (Verified VL))
  f137 : TX1_137.Args VL → Observer → Env → Obs (Except VL.WErr (Verified VL))
  f087 : TX1_087.Args VL → Observer → Env → Obs (Except VL.VErr VL.Prepared × VL.E29)
  f094 : TX1_094.Args VL → Observer → Env → Obs (Except VL.VErr Bytes)
  f328 : TX1_328.Args VL → Env → Obs (Except ProgramError Bytes)
  f345 : TX1_345.Args → Env → Obs (Except ProgramError Bytes)
  f344 : TX1_344.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)
  /-- TX2:221 = TX1:333 `process` (one function). -/
  process : TX2_221.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)
  /-- TX2:213 = TX1:330 `process_r1_cost_probe_instruction` (one function). -/
  entry : TX2_213.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)

/-! ## 4. Job deliverables -/

section Deliverables
variable (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
  (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)

/-- The existing headline and its Root0-free numeric part (no job; existing CLOSED theorems). -/
structure Headline where
  /-- `AspisR1.RPx_Deployed.deployed`. -/
  deployed : ∀ c n1 n2, S.Extraction c n1 n2 → S.Accepted1 c n1 → S.Accepted2 c n2 →
    S.Game c n1 n2 → S.Queries c n1 → S.Concl c n1 n2
  /-- `FJp_Residual.numeric` composed with `F3U_Range.per_attempt` and
  `F3U_Numeric.runtime_margin` exactly as in FJv_Top lines 129-142; it takes no
  `accepted*`, `game` or `admission*` binder. -/
  numeric : ∀ c n1 n2, S.Extraction c n1 n2 → S.Queries c n1 → S.Bound c n1 n2

/-- A0 (G0 job): the extraction binder at `native := model`. -/
structure A0_Digest where
  /-- `⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, digestSource⟩`. -/
  extraction : ∀ c, S.Exhibited c → S.Extraction c (S.model1 c) (S.model2 c)

/-- NMM_ (TX2:217, TX2:234): leaf roots. -/
structure NMM_Roots where
  r217 : TX2_217.RowSpec_217 I.f217
  r234 : TX2_234.RowSpec_234 L D I.f234

/-- NMX_ (TX2:233). -/
structure NMX_Root where
  r233 : TX2_234.RowSpec_234 L D I.f234 → TX2_217.RowSpec_217 I.f217 →
    TX2_233.RowSpec_233 L D I.f233

/-- NMS_ (TX2:242, TX2:241); 241 parametric in the library (G1b). -/
structure NMS_Roots where
  r242 : TX2_233.RowSpec_233 L D I.f233 → TX2_242.RowSpec_242 L D I.f242
  r241 : ∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
    Refines064 V0 I.f064 R0 w → TX2_242.RowSpec_242 L D I.f242 →
    TX2_241.RowSpec_241 L D (lib V0 R0 w) I.f241

/-- NMV_ (TX1:344, TX2:240, G2).  240 is parametric in EVERY library. -/
structure NMV_Roots where
  r240 : ∀ V : V2Lib, TX2_241.RowSpec_241 L D V I.f241 → TX2_240.RowSpec_240 L D V I.f240
  r344 : TX1_345.RowSpec_345 VL P C I.f345 → TX1_344.RowSpec_344 VL P C I.f344
  /-- G2: under the weak library with a write-free TX2:064 law, every observation
  admitted by the 240 reference writes no account data and keeps all payloads. -/
  g2 : ∀ w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit),
    (∀ p q r, WriteFree (w p q r)) →
    ∀ a s env o, TX2_240.Ref L D (lib V0 (fun _ _ => True) w) a s env o → Frame s o

/-- RSL-form, library-parametric 221/333 and 213/330 folds.  NMW_ (merged)
proved these over NMW_RowSpecs (Aeneas-carrier equalities), not over RSL;
see TAS_WIRING.md gap W-RSL. -/
structure NMW_Roots where
  r221 : ∀ V : V2Lib, TX1_344.RowSpec_344 VL P C I.f344 → TX2_240.RowSpec_240 L D V I.f240 →
    TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process
  r213 : ∀ V : V2Lib, TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process →
    TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) I.entry

/-- NMT_ (TX1:094, TX1:328, TX1:345). -/
structure NMT_Roots where
  r094 : TX1_087.RowSpec_087 VL P I.f087 → TX1_094.RowSpec_094 VL P I.f094
  r328 : TX1_094.RowSpec_094 VL P I.f094 → TX1_328.RowSpec_328 VL P I.f328
  r345 : TX1_328.RowSpec_328 VL P I.f328 → TX1_345.RowSpec_345 VL P C I.f345

/-- NMP_ (TX1:137, TX1:087). -/
structure NMP_Roots where
  r137 : TX1_136.RowSpec_136 VL I.f136 → TX1_137.RowSpec_137 VL I.f137
  r087 : TX1_137.RowSpec_137 VL I.f137 → TX1_087.RowSpec_087 VL P I.f087

/-- NMO_ (TX1:136). -/
structure NMO_Root where
  r136 : TX1_136.RowSpec_136 VL I.f136

/-- NMN_/NMQ_ (TX2:064, CANDIDATE `NMN_064.root`) in RSL form, canonical library. -/
structure NMN_Root where
  r064 : Refines064 V0 I.f064 V0.Root0 V0.tx2auth

/-- NNC_ G1a: the Root0-free weak law of the actual TX2:064. -/
structure NNC_G1a where
  w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)
  weak : Refines064 V0 I.f064 (fun _ _ => True) w
  /-- consumed by G2 (NMV_.g2). -/
  writeFree : ∀ p q r, WriteFree (w p q r)
  /-- on the three extents, an Ok outcome of `w` means the resume header matched. -/
  okHeader : ∀ pub pr ck env o, Dom064 (lib V0 (fun _ _ => True) w) (pub, pr, ck) →
    w pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck

/-- NNC_ G1c (NMF′): Root0 at the selected TX2 occurrence or the charged event,
from Root0-free facts only.  It takes neither `accepted2` nor the canonical
TX2 roots, and never calls the headline. -/
structure NNC_NMFPrime (g : NNC_G1a S L V0 VL I) where
  Ev : S.Ctx → Prop
  root0_or_event : ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) →
    S.Game c (S.model1 c) (S.model2 c) →
    S.Extraction c (S.model1 c) (S.model2 c) →
    S.Queries c (S.model1 c) →
    S.Root0Native c ∨ Ev c

/-- NNC_ case split: NMF′'s event is the headline's event at `native1 := model`. -/
structure NNC_CaseSplit {g : NNC_G1a S L V0 VL I} (nmf : NNC_NMFPrime S L D V0 VL P C I g) where
  event_eq : ∀ c, nmf.Ev c → S.Event c (S.model1 c)

/-- NNC_ R0-rep: the native Root0 is the canonical library's Root0 on the TX2
entry payloads (snapshot law TX2:239; `V0.Root0 = NLP_InputDomain.Root0` on bytes). -/
structure NNC_R0Rep where
  rep : ∀ c a0 a6, S.Root0Native c →
    (S.args2 c).accounts.length = 7 →
    (S.args2 c).accounts[0]? = some a0 → (S.args2 c).accounts[6]? = some a6 →
    (payload a6 (S.state2 c)).length = CHECKPOINT_BYTES →
    (payload a0 (S.state2 c)).length = PROOF_ACCOUNT_BYTES →
    V0.Root0 (payload a6 (S.state2 c))
      (slice (payload a0 (S.state2 c)) AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES)

/-- NND_ A1: every returned arm of the RSL 345 reference, at an environment
agreeing with the runtime oracles, is the result of `model1`. -/
structure NND_A1 where
  stage1 : ∀ c a env o r, S.Exhibited c → S.EnvRep c env →
    TX1_345.Ref VL P C a env o → o.exit = .ret r → S.ModelRet1 c a r

/-- NND_ A2: the same for the RSL 241 reference in the CANONICAL library. -/
structure NND_A2 where
  stage2 : ∀ c a env o r, S.Exhibited c → S.EnvRep c env →
    TX2_241.Ref L D V0 a env o → o.exit = .ret r → S.ModelRet2 c a r

/-- NNE_ A3: a returned-Ok observation admitted by the 344 reference at the TX1
images is `accepted1` at `native1 := model1`. -/
structure NNE_A3 where
  accepted1 : ∀ c o, NND_A1 S VL P C → S.Exhibited c →
    TX1_344.Ref VL P C (S.args1 c) (S.state1 c) (S.env1 c) o →
    (∃ s', o.exit = .ret (.ok (), s')) → S.Out1 c o → S.Accepted1 c (S.model1 c)

/-- NNE_ A4: the same for 240 in the canonical library and `accepted2`. -/
structure NNE_A4 where
  accepted2 : ∀ c o, NND_A2 S L D V0 → S.Exhibited c →
    TX2_240.Ref L D V0 (S.args2 c) (S.state2 c) (S.env2 c) o →
    (∃ s', o.exit = .ret (.ok (), s')) → S.Out2 c o → S.Accepted2 c (S.model2 c)

/-- NNE_ A5: game (d) at the models, from Root0-free entry facts only. -/
structure NNE_A5 where
  recorded : ∀ c, NND_A1 S VL P C → S.Exhibited c →
    (∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env)) →
    (∀ a s env, ASQ8 a.data → Frame s (I.entry a s env)) →
    (∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩) →
    S.TraceRep c I.entry →
    S.Recorded1 c (S.model1 c) (S.model2 c) ∧ S.Recorded2 c (S.model1 c) (S.model2 c)

/-- NNE_ entry representation: the two headline occurrences are a stage1 and an
ASQ8 invocation. -/
structure NNE_EntryRep where
  route1 : ∀ c, S.GameFrame c → S.TraceRep c I.entry →
    TX2_221.stage1Route (S.args1 c).data = true
  route2 : ∀ c, S.GameFrame c → S.TraceRep c I.entry → ASQ8 (S.args2 c).data

end Deliverables

/-! ## 5. Route lemmas for the entry reference -/

theorem asq8_cons {data : Bytes} (h : ASQ8 data) : ∃ t, data = 65 :: t := by
  cases data with
  | nil => simp [ASQ8, REQUEST_MAGIC] at h
  | cons x t =>
    refine ⟨t, ?_⟩
    have hx : x = 65 := by
      have := congrArg List.head? h
      simpa [REQUEST_MAGIC] using this
    rw [hx]

theorem asq8_admitted {data : Bytes} (h : ASQ8 data) : TX2_221.admitted data = true := by
  unfold TX2_221.admitted
  unfold ASQ8 at h
  simp [h]

theorem asq8_not_stage1 {data : Bytes} (h : ASQ8 data) : TX2_221.stage1Route data = false := by
  obtain ⟨t, rfl⟩ := asq8_cons h
  unfold TX2_221.stage1Route
  simp

theorem stage1_cons {data : Bytes} (h : TX2_221.stage1Route data = true) :
    data = [3, 10] ∨ data = [3, 11] := by
  unfold TX2_221.stage1Route at h
  simpa using h

theorem stage1_admitted {data : Bytes} (h : TX2_221.stage1Route data = true) :
    TX2_221.admitted data = true := by
  rcases stage1_cons h with rfl | rfl <;> decide

/-- The entry reference on the stage1 route is the stage1 packet's reference. -/
theorem ref213_stage1 {L : PoolLib} {D : DeployedIds} {V : V2Lib} {S1 : TX2_221.Stage1}
    {a : TX2_213.Args} {s : SdkState} {env : Env} {o : Obs (Except ProgramError Unit × SdkState)}
    (h1 : TX2_221.stage1Route a.data = true) (h : TX2_213.Ref L D V S1 a s env o) :
    S1.ref a s env o := by
  rcases a with ⟨pid, accts, data⟩
  rcases stage1_cons h1 with hd | hd <;> (simp only at hd; subst hd) <;>
  · simp only [TX2_213.Ref, TX2_221.admitted, TX2_221.Ref, TX2_221.stage1Route] at h
    simp at h
    exact h.2.2

/-- The entry reference on ASQ8 data is the 240 reference (with its domain). -/
theorem ref213_asq8 {L : PoolLib} {D : DeployedIds} {V : V2Lib} {S1 : TX2_221.Stage1}
    {a : TX2_213.Args} {s : SdkState} {env : Env} {o : Obs (Except ProgramError Unit × SdkState)}
    (hq : ASQ8 a.data) (h : TX2_213.Ref L D V S1 a s env o) :
    TX2_240.Ref L D V a s env o := by
  rcases a with ⟨pid, accts, data⟩
  have hadm := asq8_admitted hq
  have hs1 := asq8_not_stage1 hq
  obtain ⟨t, hd⟩ := asq8_cons hq
  simp only at hadm hs1 hd
  subst hd
  simp only [TX2_213.Ref] at h
  rw [hadm] at h
  simp only [Bool.not_true] at h
  have h2 := h.2
  simp only [TX2_221.Ref, List.head?] at h2
  rw [hs1] at h2
  exact h2.2

/-- The entry reference on non-admitted data is the silent rejection. -/
theorem ref213_reject {L : PoolLib} {D : DeployedIds} {V : V2Lib} {S1 : TX2_221.Stage1}
    {a : TX2_213.Args} {s : SdkState} {env : Env} {o : Obs (Except ProgramError Unit × SdkState)}
    (hn : TX2_221.admitted a.data = false) (h : TX2_213.Ref L D V S1 a s env o) :
    o = ⟨.ret (.error .invalidInstructionData, s), []⟩ := by
  simp only [TX2_213.Ref, hn] at h
  exact h

end RSL.TAS
