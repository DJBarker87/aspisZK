import XRp_PowersScalarSub
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersSubTransport
open XRp_PowersScalarSub

theorem sub (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    XRn_Join_Field.field.M31.sub a b = AspisR1Qm31ArithmeticProbe.field.M31.sub a b := by
  have had := XRp_CheckedWrapping.add a 2147483647#u32 (by scalar_tac)
  have hv : (U32.wrapping_add a 2147483647#u32).val = a.val + 2147483647 := by
    have h := UScalar.wrapping_add_val_eq a 2147483647#u32
    simp only [UScalar.size_def,UScalarTy.numBits] at h
    change (U32.wrapping_add a 2147483647#u32).val = (a.val+2147483647) % 4294967296 at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    exact h
  calc
    XRn_Join_Field.field.M31.sub a b = wrappingSub (U32.wrapping_add a 2147483647#u32) b := source a b
    _ = checkedSub (U32.wrapping_add a 2147483647#u32) b := subtract _ _ (by scalar_tac)
    _ = (do let x ← a+2147483647#u32; checkedSub x b) := by rw [had]; rfl
    _ = AspisR1Qm31ArithmeticProbe.field.M31.sub a b := (target a b).symm

#print axioms sub
end XRp_PowersSubTransport
