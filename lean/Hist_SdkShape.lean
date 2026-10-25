import Hist_WriterShape
import WAdm_OriginalEndpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_SdkShape
open Aeneas Aeneas.Std Result Hist_Store S2W_NativeConsolidation

/-- On the SAME exported source cuts, the original writer call supplies both
initialization and physical size, with no separately admitted writer result. -/
theorem on_cuts {CoreError : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (e1 : S2W_D189Entry.Entry) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      e1.first accounts2 saved f s)
    (owner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual ops reserved query geo B std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    Initialized saved.deref ∧ saved.val.length = 1768 := by
  obtain ⟨run,_,_,_,_,_,writer,_,_,_,_⟩ :=
    WAdm_OriginalEndpoint.reached adapter ops reserved query geo B std e1 accounts2 saved f s cuts owner ports
  exact Hist_WriterShape.installed_shape _ _ _ _ _ _ _ writer

#print axioms on_cuts
end AspisR1.Hist_SdkShape
end
