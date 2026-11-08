import NNH_Run5bCtx
import RPx_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bClaims
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open S2W_D189Consolidation S2W_NativeConsolidation S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_Run5bCtx FS FS2 MultiproofConeCanonical
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
#print axioms conclusion
end AspisR1.NNH_Run5bClaims
end
