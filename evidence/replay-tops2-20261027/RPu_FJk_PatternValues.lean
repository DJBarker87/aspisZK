import RPu_FJk_PatternModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PatternValues
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
/-- Complete source pattern VALUES on SAME powers/openings/descriptors. -/
theorem value (a : Array field.QM31 16#usize) (lambda : field.QM31)
    (out : Array field.QM31 14#usize) (ha : canonical a) (hl : Canon lambda)
    (run : pattern_values a lambda=ok out) :
    canonical out ∧ decoded out=R0P.copyPatternValuesLiteral (decoded a) (decode lambda) := by
  obtain ⟨powers,_,pv,co,ov⟩ := FJk_PatternValuesRaw.value a lambda out ha hl run
  refine ⟨co,ov.trans ?_⟩
  funext j
  exact FJk_PatternModel.value a powers lambda pv j
#print axioms value
end AspisR1.FJk_PatternValues
end
