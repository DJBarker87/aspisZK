import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SamplerGuardedOpsV1

theorem shift32_agree (r : U64) :
    (r <<< 32#i32 : Result U64) = .ok (U64.wrapping_shl r 32#u32) := by
  rfl

theorem sub_agree {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≤ x.val) :
    UScalar.sub x y = .ok (UScalar.wrapping_sub x y) := by
  obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := x) (y := y) h)
  change (x - y : Result (UScalar ty)) = .ok (UScalar.wrapping_sub x y)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, UScalar.wrapping_sub_val_eq]
  have hx := x.hSize
  have hy := y.hSize
  have he : x.val + (UScalar.size ty - y.val) = (x.val-y.val) + UScalar.size ty := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

#print axioms shift32_agree
#print axioms sub_agree
end AspisR1S9SamplerGuardedOpsV1
