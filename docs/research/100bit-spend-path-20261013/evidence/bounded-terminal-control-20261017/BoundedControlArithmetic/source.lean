import Aeneas
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisBoundedControl.Arithmetic
open Aeneas Aeneas.Std Result WP

/-- The low-bit primitive itself agrees with the natural-number model. -/
theorem low_bit_value (index : Std.U64) :
    (index &&& (1#u64)).val = index.val &&& 1 := by
  change (index.bv &&& (1#u64).bv).toNat = index.val &&& 1
  rw [BitVec.toNat_and]
  rfl

theorem low_bit_zero_iff (index : Std.U64) :
    (index &&& (1#u64)) = 0#u64 ↔ (index.val &&& 1) = 0 := by
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    rw [low_bit_value] at hv
    exact hv
  · intro h
    apply UScalar.eq_of_val_eq
    rw [low_bit_value]
    exact h

/-- The bounded candidate's shift is an ordinary one-bit unsigned shift. -/
theorem shift_one_value (index : Std.U64) :
    (Std.U64.wrapping_shr index 1#u32).val = index.val >>> 1 := by
  change (Std.U64.wrapping_shr index 1#u32).bv.toNat = index.val >>> 1
  rw [Std.U64.wrapping_shr_bv_eq]
  change (index.bv.ushiftRight 1).toNat = index.val >>> 1
  exact BitVec.toNat_ushiftRight index.bv 1

/-- Below the twenty-level bound the source increment cannot wrap. -/
theorem increment_value (carry : Std.Usize) (h : carry.val < 20) :
    (Std.Usize.wrapping_add carry 1#usize).val = carry.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hsize : 20 < UScalar.size .Usize := by
    simp only [UScalar.size, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> norm_num
  have hsmall : carry.val + (1#usize).val < UScalar.size .Usize := by
    change carry.val + 1 < UScalar.size .Usize
    omega
  exact Nat.mod_eq_of_lt hsmall

/-- A single fixed shift, independent of amount or loop values. -/
theorem amount_limit :
    Std.U32.wrapping_shl 1#u32 30#u32 = 1073741824#u32 := by rfl

#print axioms low_bit_value
#print axioms low_bit_zero_iff
#print axioms shift_one_value
#print axioms increment_value
#print axioms amount_limit
end AspisBoundedControl.Arithmetic
