import R1Z.PV_RunJoin_CircleNeutralWord53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCast53
theorem up_val (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.val
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have hx := x.hBounds; change x.val < 4294967296 at hx;omega)

theorem down_val (x : U64) (hx : x.val < 4294967296) :
    (UScalar.cast .U32 x).val = x.val := by
  change (x.bv.setWidth 32).toNat = x.val
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt hx

theorem up_down (x : U64) (hx : x.val < 4294967296) :
    UScalar.cast .U64 (UScalar.cast .U32 x) = x := by
  apply UScalar.eq_of_val_eq
  rw [up_val,down_val _ hx]

theorem down_up (x : U32) : UScalar.cast .U32 (UScalar.cast .U64 x) = x := by
  apply UScalar.eq_of_val_eq
  rw [down_val,up_val]
  rw [up_val]
  exact x.hBounds

#print axioms up_val
#print axioms down_val
#print axioms up_down
#print axioms down_up
end R1Z.PV_RunJoin_CircleNeutralCast53
