import M31RetryOutputMassNat
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber

noncomputable def retryMass (o : Option Value) : ℚ :=
  (Nat.card (AnyOutputFiber o) : ℚ) / (natTotalMass : ℚ)

theorem retryMass_none :
    retryMass none = (2 : ℚ) ^ 16 / ((2 : ℚ) ^ 32) ^ 16 := by
  unfold retryMass
  change (natNoneMass : ℚ) / (natTotalMass : ℚ) = _
  rw [natNoneMass_eq_abort, natTotalMass_eq_word_pow]
  norm_num

theorem retryMass_none_pow :
    retryMass none = (1 : ℚ) / (2 : ℚ) ^ 496 := by
  rw [retryMass_none]
  field_simp

theorem retryMass_some (r : Value) :
    retryMass (some r) =
      (1 - (2 : ℚ) ^ 16 / ((2 : ℚ) ^ 32) ^ 16) / (P31 : ℚ) := by
  unfold retryMass
  rw [natTotalMass_eq_word_pow]
  have hNat := natEachOutputCard_mul_P31 r
  have hle : 2 ^ 16 ≤ (2 ^ 32) ^ 16 := by norm_num
  have hrat :
      (Nat.card (AnyOutputFiber (some r)) : ℚ) * (P31 : ℚ) =
        ((2 : ℚ) ^ 32) ^ 16 - (2 : ℚ) ^ 16 := by
    exact_mod_cast hNat
  have hP : (P31 : ℚ) ≠ 0 := by norm_num [P31]
  have hN : ((2 : ℚ) ^ 32) ^ 16 ≠ 0 := by positivity
  have hexp : 32 * 16 = 16 + 496 := by omega
  have hpow : ((2 : ℚ) ^ 32) ^ 16 = (2 : ℚ) ^ 16 * (2 : ℚ) ^ 496 := by
    rw [← pow_mul, ← pow_add, hexp]
  field_simp [hP, hN]
  calc
    (Nat.card (AnyOutputFiber (some r)) : ℚ) * (2 : ℚ) ^ 496 * (P31 : ℚ)
        = ((Nat.card (AnyOutputFiber (some r)) : ℚ) * (P31 : ℚ)) * (2 : ℚ) ^ 496 := by ring
    _ = (((2 : ℚ) ^ 32) ^ 16 - (2 : ℚ) ^ 16) * (2 : ℚ) ^ 496 := by rw [hrat]
    _ = ((2 : ℚ) ^ 32) ^ 16 * ((2 : ℚ) ^ 496 - 1) := by rw [hpow]; ring

#print axioms retryMass_none
#print axioms retryMass_none_pow
#print axioms retryMass_some

end M31RetryOutputFiber
