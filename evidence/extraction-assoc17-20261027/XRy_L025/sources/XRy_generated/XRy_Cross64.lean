import XRy_Reducer64
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRy_Cross64
open XRp_PowersComplex
abbrev widen (x : U32) := core.convert.num.FromU64U32.from x

theorem sum_value (a b : U32) :
 (U64.wrapping_add (widen a) (widen b)).val = a.val+b.val := by
 rw [UScalar.wrapping_add_val_eq]
 simp only [UScalar.size_def,UScalarTy.numBits]
 rw [AspisR1.ExtractedCurrentCM31Mul.widen_value,
   AspisR1.ExtractedCurrentCM31Mul.widen_value]
 apply Nat.mod_eq_of_lt
 have ha : a.val ≤ 4294967295 := by scalar_tac
 have hb : b.val ≤ 4294967295 := by scalar_tac
 omega

theorem fragment (a b : EC) (ha : Canonical a) (hb : Canonical b) :
 AspisR1.ExtractedCurrentCM31Mul.generatedCrossFragment (toC a) (toC b) =
 ok (U64.wrapping_mul (U64.wrapping_add (widen a.a) (widen a.b))
   (U64.wrapping_add (widen b.a) (widen b.b))) := by
 have hleft : (widen a.a).val+(widen a.b).val < 18446744073709551616 := by
   rw [AspisR1.ExtractedCurrentCM31Mul.widen_value,
     AspisR1.ExtractedCurrentCM31Mul.widen_value]
   omega
 have hright : (widen b.a).val+(widen b.b).val < 18446744073709551616 := by
   rw [AspisR1.ExtractedCurrentCM31Mul.widen_value,
     AspisR1.ExtractedCurrentCM31Mul.widen_value]
   omega
 have hprod : (U64.wrapping_add (widen a.a) (widen a.b)).val *
   (U64.wrapping_add (widen b.a) (widen b.b)).val < 18446744073709551616 := by
   rw [sum_value,sum_value]
   have h1 : a.a.val+a.b.val < 4294967296 := by rcases ha with ⟨h1,h2⟩; omega
   have h2 : b.a.val+b.b.val < 4294967296 := by rcases hb with ⟨h1,h2⟩; omega
   exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
 unfold AspisR1.ExtractedCurrentCM31Mul.generatedCrossFragment
 simp only [toC,lift,bind_tc_ok,XRy_Reducer64.add64 _ _ hleft,
   XRy_Reducer64.add64 _ _ hright,XRy_Reducer64.mul64 _ _ hprod]

#print axioms sum_value
#print axioms fragment
end XRy_Cross64
