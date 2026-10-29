import R1Z.PV_RunJoin_CircleNeutralWord53
import R1Z.PV_B2_D_ReducerBounds
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralFold53
def low (x : U64) : U64 := ⟨x.bv &&& 2147483647#64⟩
def high (x : U64) : U64 := U64.wrapping_shr x 31#u32
def fold (x : U64) : U64 := U64.wrapping_add (low x) (high x)

theorem low_val (x : U64) : (low x).val = x.val % 2147483648 := by
  change (x.bv &&& 2147483647#64).toNat = x.val % 2147483648
  rw [BitVec.toNat_and]
  change x.val &&& (2^31-1) = x.val % 2147483648
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem high_val (x : U64) : (high x).val = x.val / 2147483648 := by
  unfold high U64.wrapping_shr UScalar.wrapping_shr
  simp only [UScalar.val,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rfl

theorem fold_val (x : U64) : (fold x).val = x.val % 2147483648+x.val / 2147483648 := by
  unfold fold
  rw [PV_RunJoin_CircleNeutralWord53.add64,low_val,high_val]
  have hx := x.hBounds
  change x.val < 18446744073709551616 at hx
  rw [low_val,high_val]
  omega

theorem fold_bound (x : U64) : (fold x).val ≤ 10737418238 := by
  rw [fold_val]
  have hx := x.hBounds
  change x.val < 18446744073709551616 at hx
  omega

theorem fold_twice_bound (x : U64) : (fold (fold x)).val < 4294967294 := by
  rw [fold_val]
  have hx := fold_bound x
  omega

#print axioms low
#print axioms high
#print axioms fold
#print axioms low_val
#print axioms high_val
#print axioms fold_val
#print axioms fold_bound
#print axioms fold_twice_bound
end R1Z.PV_RunJoin_CircleNeutralFold53
