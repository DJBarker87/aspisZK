import XRp_PowersScalarSub
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace XRq_AddValue
/-- Separate opaque value lemma prevents kernel conversion from expanding
wrapping arithmetic inside the later subtraction composition. -/
theorem val (a b : U32) (h : a.val+b.val < 4294967296) :
 (U32.wrapping_add a b).val = a.val+b.val := by
 have hw := UScalar.wrapping_add_val_eq a b
 simp only [UScalar.size_def,UScalarTy.numBits] at hw
 change (U32.wrapping_add a b).val = (a.val+b.val)%4294967296 at hw
 exact hw.trans (Nat.mod_eq_of_lt h)

theorem offset_bound (a b : U32) (ha : a.val<2147483647)
 (hb : b.val<2147483647) : b.val ≤ (U32.wrapping_add a 2147483647#u32).val := by
 rw [val a 2147483647#u32 (by scalar_tac)]
 change b.val ≤ a.val+2147483647
 omega
#print axioms val
#print axioms offset_bound
end XRq_AddValue
