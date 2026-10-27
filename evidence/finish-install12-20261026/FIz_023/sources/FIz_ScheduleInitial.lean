import FIz_ScheduleNodes
import FIz_InitialShape
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
  rw [FIz_InitialShape.value]
  unfold R0P.scheduleInitial
  simp only [FIz_Marginals.high s lm,FIz_Marginals.low s hm,←FIz_ScheduleNodes.value s lm]
  simp only [FIx_ScheduleModel.initialRaw,FIx_ScheduleModel.fullRate,FIx_ScheduleModel.full,
    FIx_ScheduleModel.firstCommon,FIx_ScheduleModel.variant,FIx_ScheduleModel.low,FIx_ScheduleModel.high,
    FIx_ScheduleModel.domain,FIx_ScheduleModel.length,FIx_ScheduleModel.noteFirst,FIw_PublicModel.openings]
  have e8 : j=(8 : Fin 16) ↔ j.val=8 := by exact Fin.ext_iff
  have e9 : j=(9 : Fin 16) ↔ j.val=9 := by exact Fin.ext_iff
  simp only [e8,e9]
  by_cases h8 : j.val=8 <;> by_cases h9 : j.val=9 <;>
    simp only [h8,h9,↓reduceIte] <;> try omega <;> rfl
#print axioms value
end AspisR1.FIz_ScheduleInitial
end
