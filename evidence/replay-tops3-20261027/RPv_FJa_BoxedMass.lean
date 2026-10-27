import RPv_FJa_ExpansionMass
import RPv_FJa_SlicesValue
import RPv_FJa_BoxedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_BoxedMass
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
/-- Both literal 64/16 selector masses are DERIVED from the original boxed
constructor on the SAME canonical point; neither is assumed. -/
theorem value (point : Array NQ 10#usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hp : FIw_ArrayValue.canonical point)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    (∑ h : Fin 64,FIv_NativeArray.value s.high h.val)=1 ∧
    (∑ l : Fin 16,FIv_NativeArray.value s.low l.val)=1 := by
  obtain ⟨hi,lo,hhi,hhigh,hlo,hlow⟩ := FIz_BoxedOrigins.value point s run
  have hv := FJa_SlicesValue.high point hi hhi
  have lv := FJa_SlicesValue.low point lo hlo
  constructor
  · exact FJa_ExpansionMass.value 64#usize hi s.high (FJa_SliceBounds.high point hi hp hhi)
      (by rw [hv.2];decide) hhigh
  · exact FJa_ExpansionMass.value 16#usize lo s.low (FJa_SliceBounds.low point lo hp hlo)
      (by rw [lv.2];decide) hlow
#print axioms value
end AspisR1.FJa_BoxedMass
end
