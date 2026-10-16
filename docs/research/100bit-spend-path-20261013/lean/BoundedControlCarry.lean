import BoundedControlSource
import BoundedControlArithmetic
import R0P.Digest
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisBoundedControl.Carry
open Aeneas Aeneas.Std Result
open AspisBoundedControl Arithmetic

/-- Fuel is proof-only: the executable candidate still has its actual loop.
The invariant fixes precisely the unobserved suffix of the twenty low bits. -/
theorem loop_success (fuel : Nat) (index : Std.U64) (carry : Std.Usize)
    (hinv : carry.val + fuel = 20) :
    ∃ out : Std.Usize, bounded_carry_loop index carry = .ok out ∧
      out.val = carry.val + R0P.digestTrailingOnes fuel index.val := by
  induction fuel generalizing index carry with
  | zero =>
    have hc : ¬ carry < 20#usize := by change ¬ carry.val < 20; omega
    refine ⟨carry, ?_, ?_⟩
    · rw [bounded_carry_loop.eq_def, if_neg hc]
    · simp only [R0P.digestTrailingOnes, Nat.add_zero]
  | succ fuel ih =>
    have hcval : carry.val < 20 := by omega
    have hc : carry < 20#usize := by exact hcval
    by_cases hz : (index.val &&& 1) = 0
    · have hb := (low_bit_zero_iff index).mpr hz
      refine ⟨carry, ?_, ?_⟩
      · rw [bounded_carry_loop.eq_def, if_pos hc]
        change (if (index &&& 1#u64) = 0#u64 then (Result.ok carry : Result Std.Usize) else _) = .ok carry
        rw [if_pos hb]
      · simp only [R0P.digestTrailingOnes, if_pos hz, Nat.add_zero]
    · have hb : ¬ (index &&& 1#u64) = 0#u64 := by
        intro h; exact hz ((low_bit_zero_iff index).mp h)
      let index1 := Std.U64.wrapping_shr index 1#u32
      let carry1 := Std.Usize.wrapping_add carry 1#usize
      have hcarry : carry1.val = carry.val + 1 := increment_value carry hcval
      have hindex : index1.val = index.val >>> 1 := shift_one_value index
      obtain ⟨out, hout, hval⟩ := ih index1 carry1 (by omega)
      refine ⟨out, ?_, ?_⟩
      · rw [bounded_carry_loop.eq_def, if_pos hc]
        change (if (index &&& 1#u64) = 0#u64 then (Result.ok carry : Result Std.Usize) else
          bounded_carry_loop index1 carry1) = .ok out
        rw [if_neg hb]
        exact hout
      · rw [hval, hcarry, hindex]
        simp only [R0P.digestTrailingOnes, if_neg hz]
        omega

/-- Exact source execution returns the existing model's carry, for every u64.
There is no intrinsic-result or independently supplied carry premise. -/
theorem bounded_carry_is_digestCarry (index : Std.U64) :
    ∃ out : Std.Usize, bounded_carry index = .ok out ∧
      out.val = R0P.digestCarry index.val ∧ out.val ≤ 20 := by
  obtain ⟨out, hout, hval⟩ := loop_success 20 index 0#usize (by rfl)
  have hzero : (0#usize).val = 0 := by rfl
  rw [hzero, Nat.zero_add] at hval
  refine ⟨out, hout, ?_, ?_⟩
  · exact hval
  · have hbound := R0P.digest_carry_le index.val
    change out.val = R0P.digestCarry index.val at hval
    omega

#print axioms loop_success
#print axioms bounded_carry_is_digestCarry
end AspisBoundedControl.Carry
