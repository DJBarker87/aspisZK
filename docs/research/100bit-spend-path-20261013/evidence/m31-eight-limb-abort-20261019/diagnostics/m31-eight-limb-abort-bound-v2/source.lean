import M31EightLimbOutputLaw
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev EightSuccessProp (xs : EightRetryInputs) : Prop :=
  ∀ i : Fin 8, ∃ r : Value, output decode31 (xs i) = some r
abbrev EightAbortInput := {xs : EightRetryInputs // ¬ EightSuccessProp xs}

noncomputable def eightAbortMass : ℚ :=
  (Nat.card EightAbortInput : ℚ) / (Nat.card EightRetryInputs : ℚ)

theorem abortProp_iff_some_none (xs : EightRetryInputs) :
    (∃ i : Fin 8, output decode31 (xs i) = none) ↔ ¬ EightSuccessProp xs := by
  constructor
  · rintro ⟨i, hi⟩ hsuccess
    obtain ⟨r, hr⟩ := hsuccess i
    rw [hi] at hr
    cases hr
  · intro hnot
    by_contra hnone
    apply hnot
    intro i
    cases h : output decode31 (xs i) with
    | none => exact False.elim (hnone ⟨i, h⟩)
    | some r => exact ⟨r, h⟩

theorem eightAbort_card_exact :
    Nat.card EightAbortInput = (2 ^ 32) ^ 128 - ((2 ^ 32) ^ 16 - 2 ^ 16) ^ 8 := by
  classical
  letI : Fintype EightRetryInputs := inferInstance
  letI : Fintype EightSuccessInput := inferInstance
  letI : Fintype EightAbortInput := inferInstance
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  change Fintype.card {xs : EightRetryInputs // ¬ EightSuccessProp xs} =
    Fintype.card EightRetryInputs - Fintype.card EightSuccessInput
  rw [Fintype.card_subtype_compl]
  rw [eightRetryInput_card, eightSuccessInput_card_exact]
  simp only [pow_mul]

theorem pow_failure_union_bound (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    1 - (1 - p) ^ n ≤ (n : ℚ) * p := by
  have hbase0 : 0 ≤ 1 - p := by linarith
  have hbase1 : 1 - p ≤ 1 := by linarith
  have hpow : ∀ n : Nat, 0 ≤ (1 - p) ^ n ∧ (1 - p) ^ n ≤ 1 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      constructor
      · exact mul_nonneg ih.1 hbase0
      · calc
          (1 - p) ^ m * (1 - p) ≤ 1 * 1 :=
            mul_le_mul ih.2 hbase1 hbase0 (by norm_num)
          _ = 1 := by norm_num
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      calc
        1 - (1 - p) ^ n * (1 - p) = (1 - (1 - p) ^ n) + (1 - p) ^ n * p := by ring
        _ ≤ (n : ℚ) * p + p :=
          add_le_add ih (mul_le_mul_of_nonneg_right (hpow n).2 hp0)
        _ = ((n + 1 : Nat) : ℚ) * p := by push_cast; ring

theorem eightAbortMass_exact :
    eightAbortMass = 1 - (1 - (1 : ℚ) / (2 : ℚ) ^ 496) ^ 8 := by
  unfold eightAbortMass
  rw [eightAbort_card_exact, eightRetryInput_card]
  let S : Nat := (2 ^ 32) ^ 16 - 2 ^ 16
  let T : Nat := (2 ^ 32) ^ 16
  have hle : S ^ 8 ≤ T ^ 8 := by
    apply Nat.pow_le_pow_left
    dsimp [S, T]
    exact Nat.sub_le _ _
  have hTpos : (T : ℚ) ≠ 0 := by
    dsimp [T]
    positivity
  have hcast : ((T ^ 8 - S ^ 8 : Nat) : ℚ) = (T : ℚ) ^ 8 - (S : ℚ) ^ 8 := by
    exact_mod_cast Nat.cast_sub hle
  have hsingle : (S : ℚ) / (T : ℚ) = 1 - (1 : ℚ) / (2 : ℚ) ^ 496 := by
    dsimp [S, T]
    have hle' : 2 ^ 16 ≤ (2 ^ 32) ^ 16 := by norm_num
    have hcast' : (((2 ^ 32) ^ 16 - 2 ^ 16 : Nat) : ℚ) =
        ((2 : ℚ) ^ 32) ^ 16 - (2 : ℚ) ^ 16 := by
      exact_mod_cast Nat.cast_sub hle'
    rw [hcast']
    have hpow : ((2 : ℚ) ^ 32) ^ 16 = (2 : ℚ) ^ 16 * (2 : ℚ) ^ 496 := by
      calc
        ((2 : ℚ) ^ 32) ^ 16 = (2 : ℚ) ^ (32 * 16) := by rw [pow_mul]
        _ = (2 : ℚ) ^ (16 + 496) := by congr 1 <;> omega
        _ = (2 : ℚ) ^ 16 * (2 : ℚ) ^ 496 := by rw [pow_add]
    rw [hpow]
    field_simp
    <;> ring
  rw [hcast]
  calc
    ((T : ℚ) ^ 8 - (S : ℚ) ^ 8) / (T : ℚ) ^ 8 =
        1 - ((S : ℚ) / (T : ℚ)) ^ 8 := by
          field_simp [hTpos]
          <;> ring
    _ = 1 - (1 - (1 : ℚ) / (2 : ℚ) ^ 496) ^ 8 := by rw [hsingle]

theorem eightAbortMass_le_union_bound :
    eightAbortMass ≤ 8 * ((1 : ℚ) / (2 : ℚ) ^ 496) := by
  rw [eightAbortMass_exact]
  apply pow_failure_union_bound
  · positivity
  · norm_num

#print axioms abortProp_iff_some_none
#print axioms eightAbort_card_exact
#print axioms pow_failure_union_bound
#print axioms eightAbortMass_exact
#print axioms eightAbortMass_le_union_bound

end M31RetryOutputFiber
