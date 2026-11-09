import NNH_Run5bHost
import NOC_Op9
import LIBC_Filled
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_HostSeed
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Faithful model of the frozen `aspis_core::r0::heap::filled` (heap.rs:5-10 at
4bb3b3f): `try_reserve_exact` outcome is the configuration's reservation bit;
success yields `n` copies, failure yields `Error::Allocation`. Same body as
JGp_Allocation.filled except that the reservation is the argument, not `true`. -/
def filled (reserved : Bool) {T : Type} (_copy : core.marker.Copy T) (n : Usize) (x : T) :
    Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) := do
  let r ← OraclePortStdAllocation.filled n x reserved
  match r with
  | .error _ => ok (.Err aspis_core.r0.Error.Allocation)
  | .ok v => ok (.Ok v)

/-- NNH_HostSeed.m0 with the single R1-reached residual, current op1, installed. -/
def m0 (reserved : Bool) : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE :=
 {NNH_HostSeed.m0 with currentBase := {NNH_HostSeed.m0.currentBase with op1 := filled reserved}}

/-- The one-line diff: restoring the old currentBase gives the old seed. -/
theorem diff (reserved : Bool) :
 {m0 reserved with currentBase := NNH_HostSeed.m0.currentBase} = NNH_HostSeed.m0 := rfl
theorem op1_slot (reserved : Bool) : (m0 reserved).currentBase.op1 = filled reserved := rfl
end AspisR1.NOC_HostSeed

namespace AspisR1.NOC_HostCtx
open Aeneas Aeneas.Std Result
abbrev Ctx := NNH_HostCtx.Ctx
abbrev envOf {W Tx : Type} (c : Ctx W Tx) : RSL.Env := NNH_HostCtx.envOf c
abbrev missingLit {W Tx : Type} (c : Ctx W Tx) :=
 NNH_Tx2Configuration.select
  (NNH_CorrectConfiguration.residual (NOC_HostSeed.m0 (envOf c).reservation) (envOf c)) (envOf c)
abbrev missing {W Tx : Type} (c : Ctx W Tx) := missingLit c
def Exhibited {W Tx : Type} (c : Ctx W Tx) : Prop := (missing c) = missingLit c
abbrev base {W Tx : Type} (c : Ctx W Tx) :=
 IDa_Deployed.deployedConfiguration (missing c) c.fixed.indexError c.fixed.reservation
abbrev configuration {W Tx : Type} (c : Ctx W Tx) :=
 FIp_Install.configuration c.fixed.indexError (base c) c.fixed.reservation
abbrev sdk {W Tx : Type} (c : Ctx W Tx) := DrvC_Installation.sdk (configuration c)
abbrev model1 {W Tx : Type} (c : Ctx W Tx) : S2W_ExtractionBoundary.First :=
 AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c)
abbrev model2 {W Tx : Type} (c : Ctx W Tx) : S2W_ExtractionBoundary.Second :=
 AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk c)
abbrev hashv {W Tx : Type} (c : Ctx W Tx) := DGP_HostDigest.hashvInst c.sha256
theorem exhibited {W Tx : Type} (c : Ctx W Tx) : Exhibited c := rfl
theorem extraction {W Tx : Type} (c : Ctx W Tx) :
 S2W_DigestExtraction.AeneasExtraction (sdk c) (model1 c) (model2 c) (hashv c) :=
 ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl,
  DGP_HostDigest.digestSource (NOC_HostSeed.m0 (envOf c).reservation) c.sha256 c.fixed.pda c.fixed.clock
   c.fixed.reservation c.fixed.indexError⟩
end AspisR1.NOC_HostCtx

namespace AspisR1.NOC_Run5bCtx
open Aeneas Aeneas.Std Result
abbrev Fixed := NNH_HostCtx.Fixed
abbrev World := NNH_HostCtx.World
abbrev Ctx := NNH_HostCtx.Ctx
abbrev envOf {W Tx : Type} (c : Ctx W Tx) := NFB_NMFBHost.env2 c
abbrev missingLit := @NOC_HostCtx.missingLit
abbrev missing := @NOC_HostCtx.missing
abbrev Exhibited := @NOC_HostCtx.Exhibited
abbrev base := @NOC_HostCtx.base
abbrev configuration := @NOC_HostCtx.configuration
abbrev sdk := @NOC_HostCtx.sdk
abbrev model1 := @NOC_HostCtx.model1
abbrev model2 := @NOC_HostCtx.model2
abbrev hashv := @NOC_HostCtx.hashv
abbrev exhibited := @NOC_HostCtx.exhibited
abbrev extraction := @NOC_HostCtx.extraction
end AspisR1.NOC_Run5bCtx

namespace AspisR1.NOC_Run5bClaims
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

def conclusion (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
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
          F3X_Projection.project select)))) ∧
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
end AspisR1.NOC_Run5bClaims

namespace AspisR1.NOC_Run5bHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx
variable {W Tx : Type}
variable (L : Library W (Nat → Record))
variable (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))

def runtime (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second) :=
 ARX_AdmittedRuntime.runtime (Tx := Tx) L copy NNE_AbortIndicator.allocator (base c)
  c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) (NNH_StateNormalize.normalize c.fixed.a)
def bound (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second) : Prop :=
 F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) ≤ F3T_Numeric.total (c.fixed.Q0+c.fixed.Q1) ∧
 (c.fixed.Q0+c.fixed.Q1 ≤ F3U_RangeEdges.maxQueries →
  F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) ≤
   (c.fixed.Q0+c.fixed.Q1+1:Rat)*(1/(2:Rat)^100)) ∧
 (c.fixed.Q0+c.fixed.Q1=0 → F3U_Numeric.margin ≤
  1/(2:Rat)^100-F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) ∧
  F3T_RuntimeBound.failureModel (runtime L copy c n1 n2) < 1/(2:Rat)^100)
def event (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First) : Prop :=
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (c.fixed.Q0+c.fixed.Q1+2965)
  (eval c.sha256 (Hiq_RecordedJoint.program
   (F3X_Account.program (configuration c) (hashv c)
    (ARW_Induced.program n1 copy NNE_AbortIndicator.allocator CPH_Program.verifier
     (NNH_StateNormalize.normalize c.fixed.a))) F3X_Projection.project
   (fun _ => P2P_NativeSelection.pair (sdk c) CPH_Program.verifier
    c.i.entry c.j.entry c.j.data c.j.slot)))
/-- Internal seed only. Physical fields below replace the marked neutral seed
fields before S_host is exposed; no theorem consumes this seed signature. -/
def seed : RSL.TAS.Sig where
 Ctx := Ctx W Tx
 First := S2W_ExtractionBoundary.First
 Second := S2W_ExtractionBoundary.Second
 model1 := model1
 model2 := model2
 Exhibited := Exhibited
 Extraction := fun c n1 n2 => S2W_DigestExtraction.AeneasExtraction (sdk c) n1 n2 (hashv c)
 Accepted1 := fun _ _ => False
 Accepted2 := fun _ _ => False
 GameFrame := fun _ => False
 Recorded1 := fun _ _ _ => False
 Recorded2 := fun _ _ _ => False
 Game := fun _ _ _ => False
 mkGame := fun _ _ _ h => False.elim h
 Queries := fun c n1 => ∀ H,
  (ARW_Induced.issued n1 copy NNE_AbortIndicator.allocator CPH_Program.verifier
   (NNH_StateNormalize.normalize c.fixed.a) H).length ≤ c.fixed.Q0+c.fixed.Q1
 Concl := NOC_Run5bClaims.conclusion L copy
 Bound := bound L copy
 Event := event copy
 args1 := fun c => NNE_EntryArgs.args c.i.entry 3 CPH_Program.verifier c.i.data
 args2 := fun c => NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data
 state1 := fun c => NNE_Entry.state c.i.entry 0
 state2 := fun c => NNE_Entry.state c.j.entry 0
 env1 := envOf
 env2 := envOf
 Out1 := fun c => NNE_PhysicalAccepted.Out1 c.world.saved
 Out2 := fun _ _ => True
 EnvRep := fun c => NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256)
  c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation
 env1_rep := fun c => NNH_HostEnv.environment_rep _ _ _ _
 env2_rep := fun c => NNH_HostEnv.environment_rep _ _ _ _
 TraceRep := fun _ _ => False
 Root0Native := fun c => NNH_Libraries.V0.Root0
  (S2W_ReturnedCheckpoint.nativeBytes (c.j.entry.buffers (c.j.entry.handles 6).1))
  (RSL.slice (S2W_ReturnedCheckpoint.nativeBytes (c.j.entry.buffers (c.j.entry.handles 0).1)) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES)
 readerHeader := NNH_G1aEnv.header
 ModelRet1 := fun _ _ _ => True
 ModelRet2 := fun _ _ _ => True

def hostRuntime : NNH_HostEnv.Runtime (Ctx W Tx) where
 sha := fun c => DGP_HostDigest.shaReply c.sha256
 pda := fun c => c.fixed.pda
 clock := fun c => NND_Carrier.reply NND_Carrier.slot c.j.slot
 reservation := fun c => c.fixed.reservation
abbrev envSig := NNH_HostEnv.install (seed (Tx := Tx) L copy) (hostRuntime (W := W) (Tx := Tx))

def data (std : S2W_TrustedStd.TrustedStd copy) : NNE_AcceptanceSig.Data (envSig (Tx := Tx) L copy) where
 err := NND_Carrier.error
 invalid := rfl
 native1 := id
 native2 := id
 e1 := fun c => c.i.entry
 e2 := fun c => c.j.entry
 program := fun _ => CPH_Program.verifier
 data1 := fun c => c.i.data
 data2 := fun c => c.j.data
 slot := fun c => c.j.slot
 saved := fun c => c.world.saved
 copy := copy
 std := std

def record : NNH_RecordSig.Data (envSig (Tx := Tx) L copy) where
 Tx := Tx
 p := fun c => c.world.p
 t := fun c => c.world.t
 u := fun c => c.world.u
 actions := fun c => c.world.actions

/-- Original runtime trust facts, retained at their selected entries.
They enter the actual-run frame, not the total arbitrary-input constructor. -/
def retained (c : Ctx W Tx) : Prop :=
 RuntimeEntrypointAdmission L c.i.entry c.world.w1 3 ∧
 RuntimeEntrypointAdmission L c.j.entry c.world.w2 7 ∧
 CPR_DataPersistence.TwoTransactionLaw (CPG_Projection.adjacent c.world.p)
  (CPG_Projection.ordinary c.world.p (Hist_Nonvacuity.key 0#u8))
  (CPG_Projection.before c.world.p) (CPG_Projection.tentative c.world.p)
  (CPG_Projection.success c.world.p) (CPG_Projection.loaded c.world.p)

def S_host (std : S2W_TrustedStd.TrustedStd copy) : RSL.TAS.Sig :=
 let S := NNH_RecordSig.physical (envSig (Tx := Tx) L copy) (data (Tx := Tx) L copy std) (record (Tx := Tx) L copy)
 {S with
  GameFrame := fun c => S.GameFrame c ∧ retained L c
  Game := fun c n1 n2 => S.Game c n1 n2 ∧ retained L c
  mkGame := fun c n1 n2 f r1 r2 => ⟨S.mkGame c n1 n2 f.1 r1 r2,f.2⟩}

def a0 (std : S2W_TrustedStd.TrustedStd copy) : RSL.TAS.A0_Digest (S_host (Tx := Tx) L copy std) where
 extraction := fun c _ => NOC_Run5bCtx.extraction c

theorem account_at (e : Entry) (n k : Nat) (hk : k < n)
 (p : S2W_ExtractionBoundary.Program) (bs : Slice U8) :
 (NNE_EntryArgs.args e n p bs).accounts[k]? = some (NNE_Entry.account e k) := by
 change ((List.range n).map (NNE_Entry.account e))[k]? = _
 rw [List.getElem?_map, List.getElem?_range hk]
 rfl

def r0 (std : S2W_TrustedStd.TrustedStd copy) :
 RSL.TAS.NNC_R0Rep (S_host (Tx := Tx) L copy std) NNH_Libraries.V0 where
 rep := by
  intro c a0 a6 h _ h0 h6 _ _
  have z := account_at c.j.entry 7 0 (by decide) CPH_Program.verifier c.j.data
  have s := account_at c.j.entry 7 6 (by decide) CPH_Program.verifier c.j.data
  have ez : a0 = NNE_Entry.account c.j.entry 0 := Option.some.inj (h0.symm.trans z)
  have es : a6 = NNE_Entry.account c.j.entry 6 := Option.some.inj (h6.symm.trans s)
  subst a0; subst a6
  exact h
end AspisR1.NOC_Run5bHost

namespace AspisR1.NOC_SeedTransfer
open Aeneas Aeneas.Std Result
abbrev oldCfg {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NNH_Run5bCtx.configuration c
abbrev newCfg {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_Run5bCtx.configuration c
/-- Every configuration field other than currentBase is the old one. -/
theorem config {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 {newCfg c with currentBase := (oldCfg c).currentBase} = oldCfg c := rfl
/-- currentBase differs from the old one in op1 only. -/
theorem currentBase {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 {(newCfg c).currentBase with op1 := (oldCfg c).currentBase.op1} = (oldCfg c).currentBase := rfl
/-- The installed current dictionary differs in op1 only. -/
theorem current {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 {DrvC_Installation.currentInstalled (newCfg c) with
   op1 := (DrvC_Installation.currentInstalled (oldCfg c)).op1} =
 DrvC_Installation.currentInstalled (oldCfg c) := rfl
theorem current_op1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 (DrvC_Installation.currentInstalled (newCfg c)).op1 =
  NOC_HostSeed.filled (NNH_HostCtx.envOf c).reservation := rfl
/-- The stage dictionary is unchanged. -/
theorem stage {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 DrvC_Installation.stage (newCfg c) = DrvC_Installation.stage (oldCfg c) := rfl
/-- The sdk differs only in op10, the current tx1 entry. -/
theorem sdk {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 {DrvC_Installation.sdk (newCfg c) with op10 := (DrvC_Installation.sdk (oldCfg c)).op10} =
 DrvC_Installation.sdk (oldCfg c) := rfl
/-- The prepared/semantic host digest is unchanged. -/
theorem digest {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NOC_Run5bCtx.sdk c)) =
 NNV_PreparedAtHost.digest c := rfl
/-- X3 at the corrected configuration (transfers by definitional unfolding). -/
theorem op9 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (pub : NNH_Libraries.VL.Public) (bytes : Slice U8)
 (sem : RSL.Verified NNH_Libraries.VL)
 (called : NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ (NOC_Run5bCtx.envOf c) = .ok sem) :
 (DrvC_Installation.currentInstalled (newCfg c)).op9
  (NNV_PreparedAtHost.digest c)
  (AspisR1CurrentCaller.FirstComposition.toCurrentPublic pub) bytes () none =
 .ok (.Ok (NNV_PreparedInputs.sem sem)) := NOC_Op9.op9 c pub bytes sem called
end AspisR1.NOC_SeedTransfer
end
#print axioms AspisR1.NOC_HostSeed.filled
#print axioms AspisR1.NOC_HostSeed.m0
#print axioms AspisR1.NOC_HostSeed.diff
#print axioms AspisR1.NOC_HostSeed.op1_slot
#print axioms AspisR1.NOC_HostCtx.exhibited
#print axioms AspisR1.NOC_HostCtx.extraction
#print axioms AspisR1.NOC_Run5bHost.S_host
#print axioms AspisR1.NOC_Run5bHost.a0
#print axioms AspisR1.NOC_Run5bHost.r0
#print axioms AspisR1.NOC_SeedTransfer.config
#print axioms AspisR1.NOC_SeedTransfer.currentBase
#print axioms AspisR1.NOC_SeedTransfer.current
#print axioms AspisR1.NOC_SeedTransfer.current_op1
#print axioms AspisR1.NOC_SeedTransfer.stage
#print axioms AspisR1.NOC_SeedTransfer.sdk
#print axioms AspisR1.NOC_SeedTransfer.digest
#print axioms AspisR1.NOC_SeedTransfer.op9
