import RPu_FIz_ScheduleNodes
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScheduleAbsorption
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors Openings)
theorem value (v : FIx_ScheduleModel.Variant) (s : Selectors) (o : Openings)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    FIx_ScheduleModel.absorption v s o=
      R0P.scheduleAbsorption (FIw_CoefficientTransport.variant v) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  funext j
  unfold R0P.scheduleAbsorption R0P.scheduleAbsorptionLiteral
  simp only [FIz_Marginals.high s lm,FIz_Marginals.low s hm,←FIz_ScheduleNodes.value s lm]
  rfl
#print axioms value
end AspisR1.FIz_ScheduleAbsorption
end
