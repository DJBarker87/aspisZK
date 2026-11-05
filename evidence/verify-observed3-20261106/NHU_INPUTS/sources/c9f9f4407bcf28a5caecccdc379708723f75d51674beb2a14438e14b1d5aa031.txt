import NHU_InterpolationRaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Interpolation
open FIq_Native

theorem source (w0 w1 w2 c0 c1 c2 : U32) :
 state_only_poseidon.interpolate_three_constant_limb w0 w1 w2 c0 c1 c2=(do
 let sum←NHU_InterpolationRaw.raw w0 w1 w2 c0 c1 c2
 field.M31.reduce_u64 sum) := by
 simp only [state_only_poseidon.interpolate_three_constant_limb,
  NHU_InterpolationRaw.raw,NHU_U64Product.product,NHU_U64Product.wide,
  FJb_WideSum4.wide,lift,bind_tc_ok,bind_assoc_eq]

theorem result (w0 w1 w2 c0 c1 c2 : U32)
 (hw0 : w0.val<2147483647) (hw1 : w1.val<2147483647) (hw2 : w2.val<2147483647)
 (hc0 : c0.val<2147483647) (hc1 : c1.val<2147483647) (hc2 : c2.val<2147483647) :
 ∃ out,state_only_poseidon.interpolate_three_constant_limb w0 w1 w2 c0 c1 c2=ok out ∧
 out.val=(w0.val*c0.val+w1.val*c1.val+w2.val*c2.val)%2147483647 ∧ out.val<2147483647 := by
 obtain ⟨sum,call,value,_⟩:=NHU_InterpolationRaw.result w0 w1 w2 c0 c1 c2 hw0 hw1 hw2 hc0 hc1 hc2
 obtain ⟨out,reduce,modulo,canonical⟩:=ExtractedMaskReducer.current_wrapper_mod sum
 refine ⟨out,?_,?_,canonical⟩
 · rw [source,call,bind_tc_ok,FIv_NativeArithmetic.m31_reduce]
   exact reduce
 · simpa only [value] using modulo
#print axioms source
#print axioms result
end AspisR1.NHU_Interpolation
