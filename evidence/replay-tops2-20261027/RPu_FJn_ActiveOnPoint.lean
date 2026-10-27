import RPu_FJn_CopySelectors
import RPu_FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_ActiveOnPoint
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (decode Canon)
open FIw_ArrayValue (canonical decoded)
/-- The source active result is activeAt of the SAME actual canonical point. -/
theorem value (point : Array field.QM31 10#usize) (s : FIw_PublicModel.Selectors)
    (out : field.QM31) (hp : canonical point)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.active s=ok out) :
    Canon out ∧ decode out=R0P.SemSource.activeAt (decoded point) := by
  have cs:=FJa_BoxedCanonical.value point s hp boxed
  have got:=FJn_ActiveValue.value s out cs.1 cs.2 run
  refine ⟨got.1,?_⟩
  rw [got.2,FJn_CopySelectors.value point s hp boxed,FJa_BoxedSelAt.value point s hp boxed]
  rfl
#print axioms value
end AspisR1.FJn_ActiveOnPoint
end
