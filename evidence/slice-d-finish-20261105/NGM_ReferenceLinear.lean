import NGM_ScalarCanon
import NGM_AddReference
import ExtractedMaskM31AddSub
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGM_ReferenceLinear
abbrev P : Nat := 2147483647

theorem add (x y : U32) (_hx : x.val<P) (_hy : y.val<P) :
 NGM_DoubleRef.add_ref x y=FIn_WeightsExtract.field.M31.add x y := by
 simp [NGM_DoubleRef.add_ref,FIn_WeightsExtract.field.M31.add,FIn_WeightsExtract.field.P,lift]
theorem sub (x y : U32) (_hx : x.val<P) (_hy : y.val<P) :
 NGM_DoubleRef.sub_ref x y=FIn_WeightsExtract.field.M31.sub x y := by
 simp [NGM_DoubleRef.sub_ref,FIn_WeightsExtract.field.M31.sub,FIn_WeightsExtract.field.P,lift]

theorem add_canonical (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z, FIn_WeightsExtract.field.M31.add x y = ok z ∧ z.val < P := by
  obtain ⟨z,hz,_,hc⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x y hx hy
  exact ⟨z, (add x y hx hy).symm.trans ((NGM_AddReference.add_reference x y hx hy).trans hz), hc⟩

#print axioms add
#print axioms sub
#print axioms add_canonical
end NGM_ReferenceLinear
