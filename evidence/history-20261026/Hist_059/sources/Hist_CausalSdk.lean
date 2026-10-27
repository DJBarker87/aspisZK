import Hist_CausalBinding
import Hist_SdkShape
import Hist_SdkKeys
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_CausalSdk
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2W_NativeConsolidation ClaimsUnrolledSdk MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Actual original SDK dictionary/cuts, concrete source owner guard and
writer marker, and runtime causal loads. No history, marker or native-writer
admission hypothesis is inserted. The same-key experiment association is named. -/
def version {CoreError : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual ops reserved query geo B std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (program : S2W_ExtractionBoundary.Program) (initial final : Store) (layout1 layout2 : Layout)
    (data1 : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      program (load initial layout1).first data1 = ok (.Ok saved))
    (events : List S2X.AccountEvent)
    (trace : Trace (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      program (commit initial (layout1.handles 2).1 saved) events final)
    (sameKey : (layout2.handles 6).1 = (layout1.handles 2).1)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdkOps (Hist_Authority.install adapter) (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      (load initial layout1).first ((load final layout2).second S2W_D189Wrappers.secondSizes) saved f s) :
    S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) := by
  have shape := Hist_SdkShape.on_cuts (Hist_Authority.install adapter) ops reserved query geo B std
    (load initial layout1) ((load final layout2).second S2W_D189Wrappers.secondSizes) saved f s cuts owner ports
  rw [Hist_SdkKeys.commute] at accepted1 trace cuts
  exact Hist_CausalBinding.version (sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
    program initial final layout1 layout2 data1 saved accepted1 events trace sameKey shape.1 f s cuts

#print axioms version
end AspisR1.Hist_CausalSdk
end
