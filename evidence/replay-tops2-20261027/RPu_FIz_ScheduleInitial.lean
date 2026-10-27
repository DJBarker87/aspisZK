import RPu_FIz_ScheduleNodes
import RPu_FIz_InitialShape
import RPu_FIz_ScheduleShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScheduleInitial
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors Openings)
theorem value (v : FIx_ScheduleModel.Variant) (s : Selectors) (o : Openings)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    FIx_ScheduleModel.initial v s o=
      R0P.scheduleInitial (FIw_CoefficientTransport.variant v) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  funext j
  rw [FIz_InitialShape.value,FIz_ScheduleShape.value]
  simp only [FIz_Marginals.high s lm,FIz_Marginals.low s hm,←FIz_ScheduleNodes.value s lm]
  rfl
#print axioms value
end AspisR1.FIz_ScheduleInitial
end
