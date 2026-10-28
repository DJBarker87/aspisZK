import Aeneas

namespace R1Z.PV_RDCD3_V260Bounds
set_option autoImplicit false
open Aeneas Aeneas.Std Result

/-- Native extra[j/28] is in bounds on exactly the reached guarded domain. -/
theorem extra (j : Nat) (guard : j < 56) : j/28 < 2 ∧ j%28 < 28 := by omega

/-- Every arithmetic operation producing a tensor shift/count is in range;
no checked overflow or shift masking changes the deployed expression. -/
theorem tensor (d : Nat) (guard : d < 5) :
    d < 5 ∧ 2*d < 64 ∧ 2*d < 2^32 ∧ 2*d < 2^64 := by omega

/-- Both point array subscripts and the one-bit shift are in range. -/
theorem point (b : Nat) (guard : b < 10) :
    9-b < 10 ∧ b < 64 ∧ b < 2^32 := by omega

/-- The special D branch's outer point subscript is always valid. -/
theorem kind_point (kind : Nat) (lo : 1 ≤ kind) (hi : kind ≤ 3) :
    kind-1 < 3 ∧ 1 ≤ kind := by omega

/-- Exact success domain for the tensor branch's outer dimension. -/
theorem kind_tensor (kind : Nat) (positive : 1 ≤ kind) :
    (if kind < 4 then kind-1 else kind-2) < 5 ↔ kind ≤ 6 := by
  split <;> omega

/-- The arithmetic in the permuted native row is within the shift width. -/
theorem tau_shifts (d tau : Nat) (hd : d < 5) (ht : tau < 5) :
    2*d < 64 ∧ 2*tau < 64 := by omega

/-- Complete scalar comparison used by Range::next; no callback law is assumed. -/
theorem scalar_lt (a b : Usize) :
    core.cmp.impls.PartialOrdUsize.lt a b = decide (a.val < b.val) := rfl

/-- A native usize increment under the range guard is also exact in the
wrapping model used by the retained extraction. -/
theorem increment (a b : Usize) (active : a.val < b.val) :
    (Usize.wrapping_add a 1#usize).val = a.val+1 := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt]
  · rfl
  · change a.val+1 < UScalar.size .Usize
    have hn : b.val < UScalar.size .Usize := by
      simpa only [UScalar.val,UScalar.size,UScalarTy.numBits] using b.bv.isLt
    omega

#print axioms extra
#print axioms tensor
#print axioms point
#print axioms kind_point
#print axioms kind_tensor
#print axioms tau_shifts
#print axioms scalar_lt
#print axioms increment
end R1Z.PV_RDCD3_V260Bounds
