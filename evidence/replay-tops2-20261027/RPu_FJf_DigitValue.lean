import RPt_FJd_SourceFactor
import RPt_FJc_WeightArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_DigitValue
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)

theorem value (a b f0 f1 f2 f3 : SQ) (ha : Canon a) (hb : Canon b)
    (run : FJd_SourceFactor.reference a b=ok [f0,f1,f2,f3]) :
    FJc_WeightArray.canonical (Array.make 4#usize [f0,f1,f2,f3]) ∧
    ∀ s : Fin 4,FJc_WeightArray.value (Array.make 4#usize [f0,f1,f2,f3]) s.val=
      FJd_PointReference.factors (decode a) (decode b) s := by
  have h := FJd_SourceFactor.value _ _ _ ha hb run
  refine ⟨h.1,?_⟩
  have hv := h.2
  simp only [List.map_cons,List.map_nil,List.cons.injEq] at hv
  rcases hv with ⟨v0,v1,v2,v3,_⟩
  intro s
  fin_cases s <;> simp only [FJc_WeightArray.value,Array.make,FJd_PointReference.factors,
    List.getElem?_cons_zero,List.getElem?_cons_succ,v0,v1,v2,v3]
#print axioms value
end AspisR1.FJf_DigitValue
end
