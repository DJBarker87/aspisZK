import Hist_CausalSdk
import Hist_CommittedPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_CommittedSdk
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open S2W_NativeConsolidation ClaimsUnrolledSdk MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Fill the EXACT runtime version slot consumed by RowOrder/D189, indexed to
actual post1 payload and actual selected checkpoint. No history field, saved
length, marker or writer admission is an extra premise. -/
def version {A CoreError : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (stdClaims : ClaimsUnrolledFinish.StdCalls)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual ops reserved query geo B stdClaims))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (program : S2W_ExtractionBoundary.Program) (initial final : Store) (layout1 layout2 : Layout)
    (data1 : Slice U8) (state final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator (load initial layout1) program data1 state = ok (.Ok (saved,post1,final1)))
    (events : List S2X.AccountEvent)
    (trace : Trace (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims)
      program (commit initial (layout1.handles 2).1 saved) events final)
    (sameKey : (layout2.handles 6).1 = (layout1.handles 2).1)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B stdClaims)
      (load initial layout1).first ((load final layout2).second secondSizes) saved f s) :
    S2X.CheckpointVersionBinding
      (payloadBytes encode (post1.payload ((load initial layout1).heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val) := by
  have native := (first_accepted native1 copy std allocator (load initial layout1) program data1 state final1 saved post1 accepted1).1
  have sourceAccepted := (extraction.stage1 program (load initial layout1).first data1).symm.trans native
  let history := Hist_CausalSdk.version adapter ops reserved query geo B stdClaims owner ports
    program initial final layout1 layout2 data1 saved sourceAccepted events trace sameKey f s cuts
  have shape := Hist_SdkShape.on_cuts (Hist_Authority.install adapter) ops reserved query geo B stdClaims
    (load initial layout1) ((load final layout2).second secondSizes) saved f s cuts owner ports
  have copied := Hist_CommittedPayload.copied _ native1 native2 hashv extraction copy std allocator
    (load initial layout1) program data1 state final1 saved post1 accepted1 shape.2
  exact Hist_CommittedPayload.committed_version _ _ _ copied history

#print axioms version
end AspisR1.Hist_CommittedSdk
end
