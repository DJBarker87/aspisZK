import FJa_LocalWeightFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_FullLowWeight
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FJa_PoseidonOrigins (Selectors fullFold)
/-- The original local-weight fold over EXACT indices1,9,10. -/
theorem value (s : Selectors) (out : NQ) (hs : FIw_ArrayValue.canonical s.local)
    (run : fullFold s=ok out) :
    Canon out ∧ decode out=FIv_NativeArray.value s.local 1+
      FIv_NativeArray.value s.local 9+FIv_NativeArray.value s.local 10 := by
  unfold fullFold at run
  simp only [FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok] at run
  have v := FJa_LocalWeightFold.value 3#usize [1#usize,9#usize,10#usize] s field.QM31.ZERO out hs FIv_NativeValue.zero.1 run
  refine ⟨v.1,?_⟩
  simpa only [FJa_LocalWeightFold.model,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,
    FIv_NativeValue.zero.2,zero_add] using v.2
#print axioms value
end AspisR1.FJa_FullLowWeight
end
