import LPk_ReturnChecks
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace LPk_Casts
open AspisR1.SamplerMachineBounds AspisR1.SamplerWord

/-- Applies to native quotient casts by K008 and digit casts by K009. -/
theorem native_cast (x : UInt64) (hx : x.toNat < B) :
    (UInt32.ofNat x.toNat).toNat = x.toNat := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hx

/-- Exact Aeneas U64-to-U32 carrier law on the same domain. -/
theorem cohort_cast (x : U64) (hx : x.val < B) :
    (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt hx

theorem native_pack (r : UInt64) (d : UInt32) (hr : r.toNat < P) :
    (machineWord r d).toNat = r.toNat * B + d.toNat := by
  exact machineWord_toNat d hr
#print axioms native_cast
#print axioms cohort_cast
#print axioms native_pack
end LPk_Casts
