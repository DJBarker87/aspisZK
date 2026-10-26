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
  funext j
  unfold R0P.scheduleInitial
  simp only [FIz_Marginals.high s lm,FIz_Marginals.low s hm,←FIz_ScheduleNodes.value s lm]
  by_cases h8 : j=8
  · subst j
    simp only [FIx_ScheduleModel.initial,Function.update_of_ne (by decide : (8 : Fin 16)≠9),Function.update_self]
    rfl
  · by_cases h9 : j=9
    · subst j
      simp only [FIx_ScheduleModel.initial,Function.update_self]
      rfl
    · simp only [FIx_ScheduleModel.initial,Function.update_of_ne h8,Function.update_of_ne h9,
        if_neg h8,if_neg h9]
      rfl
#print axioms value
end AspisR1.FIz_ScheduleInitial
end
