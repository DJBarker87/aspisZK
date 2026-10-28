import R1Z.PV_RDCD_SliceArrayBinding
set_option autoImplicit false
namespace R1Z.PV_RDCD_Index194
open Aeneas Aeneas.Std Result
/-- The release idx += 1 has its exact unbounded Nat value in every reached
    iteration, so no wrapping or checked-overflow error is discarded. -/
theorem next_val {N : Usize} (i : Usize) (hi : i < N) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt]
  · rfl
  · have hn : N.val < UScalar.size .Usize := by
      simpa only [UScalar.val,UScalar.size,UScalarTy.numBits] using N.bv.isLt
    have hi' : i.val+1 ≤ N.val := by scalar_tac
    exact lt_of_le_of_lt hi' hn
/-- Both checked reads are in range on the length-equal array instance. -/
theorem both_in_range {A B : Type} {N : Usize} (xs : Array A N) (ys : Array B N)
    (i : Usize) (hi : i < N) : i.val < xs.val.length ∧ i.val < ys.val.length := by
  rw [xs.property,ys.property]
  constructor <;> scalar_tac
#print axioms next_val
#print axioms both_in_range
end R1Z.PV_RDCD_Index194
