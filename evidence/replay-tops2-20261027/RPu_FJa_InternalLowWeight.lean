import RPu_FJa_InternalLowShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_InternalLowWeight
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FJa_PoseidonOrigins (Selectors internalFold)
/-- The ORIGINAL inclusive local fold visits EXACT2..8 and adds their values. -/
theorem value (s : Selectors) (out : NQ) (hs : FIw_ArrayValue.canonical s.local)
    (run : internalFold s=ok out) :
    Canon out ∧ decode out=FJa_LocalWeightFold.model s
      [2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize] 0 := by
  rw [FJa_InternalLowShape.value] at run
  have v := FJa_LocalWeightFold.value 7#usize _ s field.QM31.ZERO out hs FIv_NativeValue.zero.1 run
  rw [FIv_NativeValue.zero.2] at v
  exact v
#print axioms value
end AspisR1.FJa_InternalLowWeight
end
