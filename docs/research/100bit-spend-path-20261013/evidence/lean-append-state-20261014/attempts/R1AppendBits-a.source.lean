import R0P.Digest
import Mathlib.Data.Nat.Bitwise

/-! Symbolic low-bit facts for the literal bounded trailing-ones adapter.
No bound on the magnitude of the index, and no exhaustive integer evaluation,
is used. In particular the all-one, final-insertion case is retained. -/
set_option autoImplicit false
namespace AspisR1.AppendBits
open R0P

def BitZero (index level : Nat) : Prop := ((index >>> level) &&& 1) = 0

theorem bitZero_zero (index : Nat) : BitZero index 0 ↔ index % 2 = 0 := by
  simp [BitZero]

theorem bitZero_succ (index level : Nat) :
    BitZero index (level + 1) ↔ BitZero (index >>> 1) level := by
  unfold BitZero
  rw [Nat.add_comm level 1, Nat.shiftRight_add]

theorem before_carry (n index level : Nat)
    (hl : level < digestTrailingOnes n index) : ¬ BitZero index level := by
  induction n generalizing index level with
  | zero => simp [digestTrailingOnes] at hl
  | succ n ih =>
    by_cases hz : index &&& 1 = 0
    · simp [digestTrailingOnes, hz] at hl
    · simp only [digestTrailingOnes, if_neg hz] at hl
      cases level with
      | zero => simpa [BitZero] using hz
      | succ level =>
        rw [bitZero_succ]
        exact ih (index >>> 1) level (by omega)

theorem at_carry (n index : Nat) (hc : digestTrailingOnes n index < n) :
    BitZero index (digestTrailingOnes n index) := by
  induction n generalizing index with
  | zero => omega
  | succ n ih =>
    by_cases hz : index &&& 1 = 0
    · simpa [digestTrailingOnes, hz, BitZero] using hz
    · simp only [digestTrailingOnes, if_neg hz] at hc ⊢
      rw [Nat.add_comm 1, bitZero_succ]
      exact ih (index >>> 1) (by omega)

/-- Adding one clears precisely the initial one bits, sets the first zero
bit when it exists in the observed prefix, and preserves the higher bits. -/
theorem increment_bits (n index level : Nat) (hl : level < n) :
    BitZero (index + 1) level ↔
      level < digestTrailingOnes n index ∨
        (digestTrailingOnes n index < level ∧ BitZero index level) := by
  induction n generalizing index level with
  | zero => omega
  | succ n ih =>
    by_cases hz : index &&& 1 = 0
    · have hm : index % 2 = 0 := by simpa using hz
      simp only [digestTrailingOnes, if_pos hz]
      cases level with
      | zero => rw [bitZero_zero]; omega
      | succ level =>
        have hs : (index + 1) >>> 1 = index >>> 1 := by
          simp only [Nat.shiftRight_eq_div_pow, pow_one]
          omega
        rw [bitZero_succ, hs, bitZero_succ]
        simp
    · have hm : index % 2 = 1 := by
        have hm' : index % 2 ≠ 0 := by simpa using hz
        omega
      simp only [digestTrailingOnes, if_neg hz]
      cases level with
      | zero => rw [bitZero_zero]; omega
      | succ level =>
        have hs : (index + 1) >>> 1 = (index >>> 1) + 1 := by
          simp only [Nat.shiftRight_eq_div_pow, pow_one]
          omega
        rw [bitZero_succ, hs, bitZero_succ]
        have hb := ih (index >>> 1) level (by omega)
        omega

#print axioms before_carry
#print axioms at_carry
#print axioms increment_bits
end AspisR1.AppendBits
