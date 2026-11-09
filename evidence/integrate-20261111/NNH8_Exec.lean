import NOC_Run5bHost
import NNH_Run5bHeadlineB
set_option autoImplicit false
noncomputable section
/-! Run 7 (G0 FINAL): restatement at the corrected host AspisR1.NOC_Run5bHost.S_host
(seed NOC_HostSeed.m0: current op1 installed). Bodies are those of NNH_Run5bSplit,
Exec, Headline, HeadlineB and Acceptance with the host namespaces swapped
(NNH_Run5bCtx/Host/Claims -> NOC_Run5bCtx/Host/Claims) and the literal seed
NNH_HostSeed.m0 replaced by NOC_HostSeed.m0 at the environment's own reservation
bit. No hypothesis is added, removed or reordered. -/
namespace AspisR1.NNH8_Split
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open S2W_D189Consolidation S2W_NativeConsolidation S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx FS FS2 MultiproofConeCanonical
open S2W_AuthenticatedInputs S2W_InputSchedule S2W_ExpandedChildren S2W_TraceSplice S2W_EntryWriteHistory
variable {W Tx : Type}
variable (L : Library W (Nat → Record))
variable (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))

def rest (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
 (native2 : S2W_ExtractionBoundary.Second) : Prop :=
 let c := base ctx
 let indexError := ctx.fixed.indexError
 let reservation := ctx.fixed.reservation
 let allocator := NNE_AbortIndicator.allocator
 let e1 := ctx.i.entry
 let e2 := ctx.j.entry
 let w1 := ctx.world.w1
 let w2 := ctx.world.w2
 let data1 := ctx.i.data
 let data2 := ctx.j.data
 let slot := ctx.j.slot
 let saved := ctx.world.saved
 let post1 := writeBracket ctx.i.entry.heap 2 0 0 (source (nativeBytes ctx.world.saved))
 let post2 := ctx.j.entry.heap
 let hashv := hashv ctx
 let H := ctx.sha256
 let prior := ctx.fixed.prior
 let p := ctx.world.p
 let t := ctx.world.t
 let u := ctx.world.u
 let D := ctx.fixed.D
 let a := NNH_StateNormalize.normalize ctx.fixed.a
 let Q0 := ctx.fixed.Q0
 let Q1 := ctx.fixed.Q1
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase (FIp_Install.configuration indexError c reservation).stageBase
        (FIp_Install.configuration indexError c reservation).finish (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query (FIp_Install.configuration indexError c reservation).geometry
        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std ∧
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))

def outcome (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
 (native2 : S2W_ExtractionBoundary.Second) : Prop :=
 let c := base ctx
 let indexError := ctx.fixed.indexError
 let reservation := ctx.fixed.reservation
 let allocator := NNE_AbortIndicator.allocator
 let e1 := ctx.i.entry
 let e2 := ctx.j.entry
 let w1 := ctx.world.w1
 let w2 := ctx.world.w2
 let data1 := ctx.i.data
 let data2 := ctx.j.data
 let slot := ctx.j.slot
 let saved := ctx.world.saved
 let post1 := writeBracket ctx.i.entry.heap 2 0 0 (source (nativeBytes ctx.world.saved))
 let post2 := ctx.j.entry.heap
 let hashv := hashv ctx
 let H := ctx.sha256
 let prior := ctx.fixed.prior
 let p := ctx.world.p
 let t := ctx.world.t
 let u := ctx.world.u
 let D := ctx.fixed.D
 let a := NNH_StateNormalize.normalize ctx.fixed.a
 let Q0 := ctx.fixed.Q0
 let Q1 := ctx.fixed.Q1
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    (FJv_DResult.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase
      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query
      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase
      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError c reservation) hashv P)
          F3X_Projection.project select))))

theorem conclusion_iff (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second) :
 NOC_Run5bClaims.conclusion L copy c n1 n2 ↔ rest L copy c n1 n2 ∧ outcome L copy c n1 n2 := by
 unfold NOC_Run5bClaims.conclusion rest outcome
 dsimp only
 constructor
 · rintro ⟨a,b,c,d,e,f,g,h,i,j,k⟩
   exact ⟨⟨a,b,c,e,f,g,h,i,j,k⟩,d⟩
 · rintro ⟨⟨a,b,c,e,f,g,h,i,j,k⟩,d⟩
   exact ⟨a,b,c,d,e,f,g,h,i,j,k⟩
end AspisR1.NNH8_Split

namespace AspisR1.NNH8_Exec
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment NOC_Run5bCtx NOC_Run5bHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

abbrev post := @NNH_Run5bExec.post
/-- The corrected seed at the environment's own reservation bit (as NOC_HostCtx). -/
abbrev seed (env : RSL.Env) := NOC_HostSeed.m0 env.reservation

/-- Seed-generic clock independence (proof of NOF_A2FieldCorrected.clockFree, restated
here to keep this module's import closure small). -/
theorem clockFree (H : Bytes → State)
 (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32) (k k' : Except RSL.ProgramError UInt64)
 (r : NP6_StdModel.Reservation) (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) :
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m (DGP_HostDigest.envInst H pda k r))
  (DGP_HostDigest.envInst H pda k r) =
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m (DGP_HostDigest.envInst H pda k' r))
  (DGP_HostDigest.envInst H pda k' r) := by
 rw [NNR_ClockFree.residual H pda k k' r m]
 unfold NNH_Tx2Configuration.select
 rw [NNR_ClockFree.modelSlots H pda k k' r]
 try rfl

/-- Corrected-host analogue of NNH_Run5bCtx.missing_at_slot. -/
theorem missing_at_slot (c : Ctx W Tx) :
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual (seed (NNH_HostCtx.envOf c)) (envOf c))
 (envOf c) = missingLit c :=
 clockFree c.sha256 c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot)
  c.fixed.clock c.fixed.reservation (seed (NNH_HostCtx.envOf c))
def ERec (fx : Fixed) (H : Bytes → State) : Prop :=
 let env := DGP_HostDigest.envInst H fx.pda fx.clock fx.reservation
 let m := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual (seed env) env) env
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
  (eval H (NNH_RecordedCharge.recorder copy
   (IDa_Deployed.deployedConfiguration m fx.indexError fx.reservation)
   fx.indexError fx.reservation (DGP_HostDigest.hashvInst H) fx.a (fx.Q0+fx.Q1)))

def recSig : RSL.EVB.RecSig (S_host (Tx := Tx) L copy std) where
 Realizes := fun c =>
  (eval c.sha256 (NNH_StateNormalize.normalize c.fixed.a).first).2 = c.i ∧
  (eval c.sha256 ((NNH_StateNormalize.normalize c.fixed.a).second c.i c.world.saved
   (post c.i c.world.saved) true)).2 = c.j
 EventRec := fun c => ERec copy c.fixed c.sha256
 SelectsPair := fun c =>
  ARQ_Observer.select (configuration c) CPH_Program.verifier
   (eval c.sha256 (NNH_RecordedCharge.source copy (base c) c.fixed.indexError
    c.fixed.reservation (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1))).2 =
  P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot

def exec : RSL.TASB.ExecB (S_host (Tx := Tx) L copy std) (recSig L copy std) where
 Fixed := Fixed
 World := World W Tx
 Oracle := Bytes → State
 In1 := FirstInputs Bool
 In2 := SecondInputs Bool
 first := fun fx H => NNH_StateNormalize.firstAt fx.a H
 second := fun fx w H i => NNH_StateNormalize.secondTop
  (eval H (fx.a.second i w.saved (post i w.saved) true)).2
 build := fun fx w H i j => ⟨fx,w,H,i,j⟩
 realizes_mk := by
  intro fx w H i j
  change ((eval H (NNH_StateNormalize.normalize fx.a).first).2 = i ∧
   (eval H ((NNH_StateNormalize.normalize fx.a).second i w.saved (post i w.saved) true)).2 = j) ↔ _
  rw [NNH_StateNormalize.first_eval,NNH_StateNormalize.second_eval]
  exact Iff.rfl
 exhibited_mk := fun _ _ _ _ _ => rfl
 QueriesF := fun fx => ∀ J K,
  (ARW_Induced.issued
   (AdapterRw.r1_pool_adapter.owned.stage1_owned
    (NNH_CorrectConfiguration.sdk (seed (DGP_HostDigest.envInst J fx.pda fx.clock fx.reservation))
     (DGP_HostDigest.envInst J fx.pda fx.clock fx.reservation) fx.indexError fx.reservation))
   copy NNE_AbortIndicator.allocator CPH_Program.verifier
   (NNH_StateNormalize.normalize fx.a) K).length ≤ fx.Q0+fx.Q1
 queries_mk := fun _ _ H _ _ h => h H
 ERec := ERec copy
 eventRec_mk := fun _ _ _ _ _ => Iff.rfl
theorem recSelect : RSL.EVB.RecSelect (S_host (Tx := Tx) L copy std) (recSig L copy std) where
 selects := by
  intro c _ ext ac queries realizes
  rcases c with ⟨fx,w,H,i,j⟩
  change (eval H (NNH_StateNormalize.normalize fx.a).first).2 = i ∧
   (eval H ((NNH_StateNormalize.normalize fx.a).second i w.saved (post i w.saved) true)).2 = j at realizes
  rw [NNH_StateNormalize.first_eval,NNH_StateNormalize.second_eval] at realizes
  have hi : NNH_StateNormalize.firstAt fx.a H = i := realizes.1
  subst i
  have hj : NNH_StateNormalize.secondAt fx.a H w.saved
   (post (NNH_StateNormalize.firstAt fx.a H) w.saved) true = j := realizes.2
  subst j
  exact NNH_StateSelect.selects copy _ fx.indexError fx.reservation _ _ _ ext H H
   (DGP_HostDigest.p1 H) (DGP_HostDigest.syscall H) fx.a w.saved
   (post (NNH_StateNormalize.firstAt fx.a H) w.saved) ac fx.Q0 fx.Q1 queries

theorem environment_nonvacuous (c : Ctx W Tx) :
 (S_host L copy std).Exhibited c ∧ (S_host L copy std).EnvRep c (envOf c) :=
 ⟨rfl,NNH_HostEnv.environment_rep _ _ _ _⟩

end AspisR1.NNH8_Exec

namespace AspisR1.NNH8_Headline
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open NOC_Run5bCtx NOC_Run5bHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (borrow : S2TrustedSdkBorrow L)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

include borrow
theorem headline : RSL.TAS.Headline (S_host (Tx := Tx) L copy std) where
 deployed := by
  intro c n1 n2 ext ac1 ac2 game queries
  exact RPx_Deployed.deployed L borrow copy std NNE_AbortIndicator.allocator
   c.i.entry c.j.entry c.world.w1 c.world.w2 game.2.1 game.2.2.1
   (missing c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256) (DGP_HostDigest.syscall c.sha256)
   c.i.data c.j.data c.j.slot true true true true c.world.saved
   (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) c.j.entry.heap
   ac1 ac2 c.fixed.root c.fixed.length c.fixed.prior c.fixed.words
   c.world.p c.world.t c.world.u c.world.actions game.1 game.2.2.2
   c.fixed.D (NNH_StateNormalize.normalize c.fixed.a) c.fixed.Q0 c.fixed.Q1 queries
 numeric := by
  intro c n1 n2 ext queries
  have owners := FJu_GlobalOwners.complete _ _ (FJv_GlobalOwners.complete c.fixed.indexError
   (base c) c.fixed.reservation (FJv_GlobalTerminal.owners (missing c)
    c.fixed.indexError c.fixed.reservation _))
  have security := FJp_Residual.numeric (Tx := Tx) L copy NNE_AbortIndicator.allocator
   (base c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   (NNH_StateNormalize.normalize c.fixed.a) std c.fixed.D c.fixed.words owners
   c.fixed.Q0 c.fixed.Q1 queries
  refine ⟨security,?_,?_⟩
  · intro range
    simpa only [NOC_Run5bHost.runtime, Nat.cast_add] using security.trans (F3U_Range.per_attempt _ range)
  · intro zero
    rw [zero] at security
    exact F3U_Numeric.runtime_margin _ security
end AspisR1.NNH8_Headline

namespace AspisR1.NNH8_HeadlineB
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open NOC_Run5bCtx NOC_Run5bHost
open AspisV8R19.MemoizedProgramLaw
open NNH8_Exec FS FS2 MultiproofConeCanonical
variable {W Tx : Type} (L : Library W (Nat → Record))
 (borrow : S2TrustedSdkBorrow L)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def outcomeRec (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
 (native2 : S2W_ExtractionBoundary.Second) : Prop :=
 let c := base ctx
 let indexError := ctx.fixed.indexError
 let reservation := ctx.fixed.reservation
 let allocator := NNE_AbortIndicator.allocator
 let e1 := ctx.i.entry
 let e2 := ctx.j.entry
 let w1 := ctx.world.w1
 let w2 := ctx.world.w2
 let data1 := ctx.i.data
 let data2 := ctx.j.data
 let slot := ctx.j.slot
 let saved := ctx.world.saved
 let post1 := writeBracket ctx.i.entry.heap 2 0 0 (source (nativeBytes ctx.world.saved))
 let post2 := ctx.j.entry.heap
 let hashv := hashv ctx
 let H := ctx.sha256
 let prior := ctx.fixed.prior
 let p := ctx.world.p
 let t := ctx.world.t
 let u := ctx.world.u
 let D := ctx.fixed.D
 let a := NNH_StateNormalize.normalize ctx.fixed.a
 let Q0 := ctx.fixed.Q0
 let Q1 := ctx.fixed.Q1
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    (FJv_DResult.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase
      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query
      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase
      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      ((NNH8_Exec.recSig L copy std).EventRec ctx))

include borrow
def headlineB : RSL.EVB.HeadlineB (S_host (Tx := Tx) L copy std) (recSig L copy std) where
 OutcomeRec := outcomeRec L copy std
 outcomeRec := by
  intro c n1 n2 ext ac1 ac2 game queries selects
  have budget : ∀ H, firstReads emptyTable (eval H
   (NNH_RecordedCharge.source copy (base c) c.fixed.indexError c.fixed.reservation
    (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1))).1 ≤ c.fixed.Q0+c.fixed.Q1+1921 := by
   intro H
   exact (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget _ _ H)
  exact NNH_OutcomeRecAccepted.accepted L borrow copy std NNE_AbortIndicator.allocator
   c.i.entry c.j.entry c.world.w1 c.world.w2 game.2.1 game.2.2.1
   (missing c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256) (DGP_HostDigest.syscall c.sha256)
   c.i.data c.j.data c.j.slot true true true true c.world.saved
   (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) c.j.entry.heap
   ac1 ac2 c.fixed.root c.fixed.length c.fixed.prior c.fixed.words
   c.world.p c.world.t c.world.u c.world.actions game.1 game.2.2.2
   c.fixed.D (NNH_StateNormalize.normalize c.fixed.a) c.fixed.Q0 c.fixed.Q1 queries
   (NNH_RecordedCharge.source copy (base c) c.fixed.indexError c.fixed.reservation
    (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1))
   ARQ_Observer.project (ARQ_Observer.select (configuration c) CPH_Program.verifier)
   (c.fixed.Q0+c.fixed.Q1) budget selects
end AspisR1.NNH8_HeadlineB

namespace AspisR1.NNH8_Acceptance
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NOC_Run5bHost NNH_Libraries
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def a3 : RSL.TAS.NNE_A3 (S_host (Tx := Tx) L0 copy std) VL P C where
 accepted1 := by
  intro c o a1 hx ref ok out
  exact (NNH_RecordSig.a3 (envSig (Tx := Tx) L0 copy) (data L0 copy std) (record L0 copy) VL P C).accepted1
   c o ⟨a1.stage1⟩ hx ref ok out

def a4 : RSL.TAS.NNE_A4 (S_host (Tx := Tx) L0 copy std) L D V0 where
 accepted2 := by
  intro c o a2 hx ref ok out
  exact (NNH_RecordSig.a4 (envSig (Tx := Tx) L0 copy) (data L0 copy std) (record L0 copy) L D V0).accepted2
   c o ⟨a2.stage2⟩ hx ref ok out

def a5 (I : RSL.TAS.Impl L V0 VL) :
 RSL.TAS.NNE_A5 (S_host (Tx := Tx) L0 copy std) L V0 VL P C I where
 recorded := by
  intro c a1 hx h1 g2 reject trace
  have h := (NNH_RecordSig.a5 (envSig (Tx := Tx) L0 copy) (data L0 copy std)
   (record L0 copy) L V0 VL P C I).recorded
  exact h c ⟨a1.stage1⟩ hx h1 g2 reject trace
theorem sig_same : AspisR1.NNH_G1aEnv.sig (S_host (Tx := Tx) L0 copy std) = S_host (Tx := Tx) L0 copy std := rfl
end AspisR1.NNH8_Acceptance
end
#print axioms AspisR1.NNH8_Split.rest
#print axioms AspisR1.NNH8_Split.outcome
#print axioms AspisR1.NNH8_Split.conclusion_iff
#print axioms AspisR1.NNH8_Exec.clockFree
#print axioms AspisR1.NNH8_Exec.missing_at_slot
#print axioms AspisR1.NNH8_Exec.recSig
#print axioms AspisR1.NNH8_Exec.exec
#print axioms AspisR1.NNH8_Exec.recSelect
#print axioms AspisR1.NNH8_Exec.environment_nonvacuous
#print axioms AspisR1.NNH8_Headline.headline
#print axioms AspisR1.NNH8_HeadlineB.headlineB
#print axioms AspisR1.NNH8_Acceptance.a3
#print axioms AspisR1.NNH8_Acceptance.a4
#print axioms AspisR1.NNH8_Acceptance.a5
#print axioms AspisR1.NNH8_Acceptance.sig_same
