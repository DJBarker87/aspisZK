import NNH8_Exec
set_option autoImplicit false
noncomputable section
/-! Run 7: NNW_ Split.rest producers restated at NOC_Run5bHost.S_host (namespace swap only). -/
namespace AspisR1.NNH8_RestSetup
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def Goal (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
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
        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std

theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 Goal L copy c n1 n2 := by
 exact ⟨P6C_Extension.boundary (hashv c) c.sha256 c.sha256
  (DGP_HostDigest.p1 c.sha256) (DGP_HostDigest.syscall c.sha256),
  DrvC_SourceEntry.same_program _ (hashv c),DrvC_Installation.aus1_dictionary _⟩
#print axioms AspisR1.NNH8_RestSetup.Goal
#print axioms AspisR1.NNH8_RestSetup.produce
end AspisR1.NNH8_RestSetup
namespace AspisR1.NNH8_RestClaims
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def Goal (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
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
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100))

theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 Goal L copy c n1 n2 := by
 let cfg := configuration c
 let a := NNH_StateNormalize.normalize c.fixed.a
 let prover := ARW_Induced.program n1 copy NNE_AbortIndicator.allocator CPH_Program.verifier a
 let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  fun _ => P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot
 have q : ∀ H, (eval H prover).1.length ≤ c.fixed.Q0+c.fixed.Q1 := by
  intro H
  rw [ARW_Induced.queries]
  exact queries H
 let selected := FIp_Install.select c.fixed.reservation (base c)
 let core := Rc2_Install.configuration (Rc5_Install.seed c.fixed.indexError selected) c.fixed.reservation
 have owners := FJu_GlobalOwners.complete _ _ (FJv_GlobalOwners.complete c.fixed.indexError
  (base c) c.fixed.reservation (FJv_GlobalTerminal.owners (missing c)
   c.fixed.indexError c.fixed.reservation _))
 have cost := FJp_Cost.source_cost core (FIo_Install.finishOps c.fixed.reservation (base c).finish)
  (FIo_Nonvacuity.arithmetic_fixed c.fixed.reservation (base c).finish).symm
  ⟨rfl,rfl,rfl⟩ (hashv c) c.fixed.D c.fixed.words prover (c.fixed.Q0+c.fixed.Q1) q select
  (F3Y_InstalledLaws.prepare c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.primitives c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.canonical c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.domain c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.multiply c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.one c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.inverse c.fixed.indexError selected c.fixed.reservation)
  owners (FJp_MatchingLaw.value c.fixed.indexError (base c) c.fixed.reservation _)
 have mass := F3Y_AccountMass.claims core (hashv c) c.fixed.D c.fixed.words prover
  (c.fixed.Q0+c.fixed.Q1) q select
 have security := FJp_Residual.numeric (Tx := Tx) L copy NNE_AbortIndicator.allocator
   (base c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   (NNH_StateNormalize.normalize c.fixed.a) std c.fixed.D c.fixed.words owners
   c.fixed.Q0 c.fixed.Q1 queries
 have numeric : NOC_Run5bHost.bound L copy c n1 n2 := by
  refine ⟨security,?_,?_⟩
  · intro range
    simpa only [NOC_Run5bHost.runtime, Nat.cast_add] using security.trans (F3U_Range.per_attempt _ range)
  · intro zero
    rw [zero] at security
    exact F3U_Numeric.runtime_margin _ security
 exact ⟨F3X_ModelClaims.claims _ c.fixed.D prover _ q,cost,mass,numeric.1,numeric.2⟩
#print axioms AspisR1.NNH8_RestClaims.Goal
#print axioms AspisR1.NNH8_RestClaims.produce
end AspisR1.NNH8_RestClaims
namespace AspisR1.NNH8_RestCopy
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
def CopyFacts (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
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
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell))

theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1) : CopyFacts L copy c n1 n2 := by
 exact PoolT_Write.accepted_verifier_writes_copy (sdk c) n1 n2 (hashv c) ext copy std
  NNE_AbortIndicator.allocator c.i.entry CPH_Program.verifier c.i.data true true c.world.saved
  (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1
#print axioms AspisR1.NNH8_RestCopy.produce
end AspisR1.NNH8_RestCopy
namespace AspisR1.NNH8_RestEvents
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 Rc2_Events.Facts (configuration c) (hashv c) n1 n2 copy NNE_AbortIndicator.allocator CPH_Program.verifier c.sha256 c.world.saved := by
 exact Rc2_Events.derive _ (hashv c) n1 n2 ext copy NNE_AbortIndicator.allocator
    CPH_Program.verifier c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256)
    (DGP_HostDigest.syscall c.sha256) c.world.saved
#print axioms AspisR1.NNH8_RestEvents.produce
end AspisR1.NNH8_RestEvents
namespace AspisR1.NNH8_RestTrace
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 CPH_Trace.Facts c.world.p c.world.t c.world.u c.world.saved n1 n2 copy NNE_AbortIndicator.allocator CPH_Program.verifier := by
 exact CPH_Trace.derive game.1
#print axioms AspisR1.NNH8_RestTrace.produce
end AspisR1.NNH8_RestTrace
namespace AspisR1.NNH8_RestRecorder
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 CPH_Recorder.Facts (configuration c) (hashv c) n1 n2 copy NNE_AbortIndicator.allocator CPH_Program.verifier c.sha256 c.world.p c.world.t c.world.u c.world.saved := by
 exact CPH_Recorder.physical c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c) n1 n2 (hashv c) ext copy NNE_AbortIndicator.allocator
    CPH_Program.verifier game.1 c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256)
    (DGP_HostDigest.syscall c.sha256)
#print axioms AspisR1.NNH8_RestRecorder.produce
end AspisR1.NNH8_RestRecorder
namespace AspisR1.NNH8_RestInstallation
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 S6N_Installation.Facts (sdk c) := by
 exact S6N_Installation.facts (configuration c)
#print axioms AspisR1.NNH8_RestInstallation.produce
end AspisR1.NNH8_RestInstallation
end
