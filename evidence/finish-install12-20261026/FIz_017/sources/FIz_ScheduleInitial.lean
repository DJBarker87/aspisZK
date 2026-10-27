import FIz_ScheduleNodes
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
  change (FIx_ScheduleModel.initial v s o : Fin 16 → K)=_
  funext j
  change Fin 16 at j
  unfold R0P.scheduleInitial
  simp only [FIz_Marginals.high s lm,FIz_Marginals.low s hm,←FIz_ScheduleNodes.value s lm]
  have bound : j.val<16 := j.isLt
  interval_cases j <;>
    simp [FIx_ScheduleModel.initial,Function.update,FIx_ScheduleModel.initialRaw,
      FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,FIx_ScheduleModel.firstCommon,
      FIx_ScheduleModel.variant,FIx_ScheduleModel.low,FIx_ScheduleModel.high,
      FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,
      FIw_PublicModel.openings]
#print axioms value
end AspisR1.FIz_ScheduleInitial
end
