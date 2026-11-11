import RPv_FJa_Expansion
import RPv_FJa_SliceBounds
import RPv_FIz_BoxedOrigins
import RPv_FJa_NativePoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_BoxedCanonical
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
/-- Both boxed selector arrays are canonical because the SAME accepted point
is canonical and the ORIGINAL 6/4 slice expansions preserve canonicality. -/
theorem value (point : Array NQ 10#usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hp : canonical point)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    canonical s.high ∧ canonical s.low := by
  obtain ⟨hi,lo,hhi,hhigh,hlo,hlow⟩ := FIz_BoxedOrigins.value point s run
  exact ⟨FJa_Expansion.canonical_result _ hi s.high (FJa_SliceBounds.high point hi hp hhi) hhigh,
    FJa_Expansion.canonical_result _ lo s.low (FJa_SliceBounds.low point lo hp hlo) hlow⟩
#print axioms value
end AspisR1.FJa_BoxedCanonical
end
