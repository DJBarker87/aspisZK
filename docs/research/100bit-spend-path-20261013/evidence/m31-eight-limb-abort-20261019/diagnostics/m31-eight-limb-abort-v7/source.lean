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
    | some r => exact ⟨r, rfl⟩

theorem eightAbort_card_exact :
    Nat.card EightAbortInput = ((2 ^ 32) ^ 16) ^ 8 - ((2 ^ 32) ^ 16 - 2 ^ 16) ^ 8 := by
  classical
  letI : Fintype EightRetryInputs := inferInstance
  letI : Fintype EightSuccessInput := inferInstance
  letI : Fintype EightAbortInput := inferInstance
  have hcard : Fintype.card EightAbortInput =
      Fintype.card EightRetryInputs - Fintype.card EightSuccessInput := by
    change Fintype.card {xs : EightRetryInputs // ¬ EightSuccessProp xs} =
      Fintype.card EightRetryInputs - Fintype.card {xs : EightRetryInputs // EightSuccessProp xs}
    exact Fintype.card_subtype_compl _
  have habort : Nat.card EightAbortInput = Fintype.card EightAbortInput :=
    Nat.card_eq_fintype_card
  have htotal : Nat.card EightRetryInputs = Fintype.card EightRetryInputs :=
    Nat.card_eq_fintype_card
  have hsuccess : Nat.card EightSuccessInput = Fintype.card EightSuccessInput :=
    Nat.card_eq_fintype_card
  calc
    Nat.card EightAbortInput = Fintype.card EightAbortInput := habort
    _ = Fintype.card EightRetryInputs - Fintype.card EightSuccessInput := hcard
    _ = Nat.card EightRetryInputs - Nat.card EightSuccessInput := by rw [← htotal, ← hsuccess]
    _ = ((2 ^ 32) ^ 16) ^ 8 - ((2 ^ 32) ^ 16 - 2 ^ 16) ^ 8 := by
      rw [eightRetryInput_card, eightSuccessInput_card_exact]

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
        _ ≤ (n : ℚ) * p + 1 * p := by
          exact add_le_add ih (mul_le_mul_of_nonneg_right (hpow n).2 hp0)
        _ = ((n + 1 : Nat) : ℚ) * p := by push_cast; ring

theorem eightAbortMass_exact :
    eightAbortMass = 1 - (1 - (1 : ℚ) / (2 : ℚ) ^ 496) ^ 8 := by
  unfold eightAbortMass
  let S : Nat := (2 ^ 32) ^ 16 - 2 ^ 16
  let T : Nat := (2 ^ 32) ^ 16
  have habort : Nat.card EightAbortInput = T ^ 8 - S ^ 8 := by
    simpa [S, T] using eightAbort_card_exact
  have htotal : Nat.card EightRetryInputs = T ^ 8 := by
    simpa [T] using eightRetryInput_card
  have hbase : S ≤ T := by
    change ((2 ^ 32) ^ 16 - 2 ^ 16) ≤ (2 ^ 32) ^ 16
    exact Nat.sub_le _ _
  have hle : S ^ 8 ≤ T ^ 8 := Nat.pow_le_pow_left hbase 8
  have hcast : ((T ^ 8 - S ^ 8 : Nat) : ℚ) = (T : ℚ) ^ 8 - (S : ℚ) ^ 8 := by
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow]
  have hle' : 2 ^ 16 ≤ (2 ^ 32) ^ 16 := by
    have hbase2 : 2 ≤ 2 ^ 32 := by norm_num
    exact Nat.pow_le_pow_left hbase2 16
  have hS : (S : ℚ) = (T : ℚ) - (2 : ℚ) ^ 16 := by
    change ((((2 ^ 32) ^ 16 - 2 ^ 16 : Nat) : ℚ)) = (((2 ^ 32) ^ 16 : Nat) : ℚ) - (2 : ℚ) ^ 16
    rw [Nat.cast_sub hle']
    rw [Nat.cast_pow, Nat.cast_pow]
    norm_num
  have hT : (T : ℚ) = (2 : ℚ) ^ 16 * (2 : ℚ) ^ 496 := by
    change (((2 ^ 32) ^ 16 : Nat) : ℚ) = (2 : ℚ) ^ 16 * (2 : ℚ) ^ 496
    rw [Nat.cast_pow, Nat.cast_pow]
    norm_num
    calc
      ((2 : ℚ) ^ 32) ^ 16 = (2 : ℚ) ^ (32 * 16) := by rw [pow_mul]
      _ = (2 : ℚ) ^ (16 + 496) := by congr 1 <;> omega
      _ = (2 : ℚ) ^ 16 * (2 : ℚ) ^ 496 := by rw [pow_add]
  have hsingle : (S : ℚ) / (T : ℚ) = 1 - (1 : ℚ) / (2 : ℚ) ^ 496 := by
    rw [hS, hT]
    have hpow : (2 : ℚ) ^ 496 ≠ 0 := pow_ne_zero 496 (by norm_num)
    field_simp [hpow]
    <;> ring
  have hTpos : (T : ℚ) ≠ 0 := by rw [hT]; exact mul_ne_zero (pow_ne_zero 16 (by norm_num)) (pow_ne_zero 496 (by norm_num))
  rw [habort, htotal, hcast]
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
  · have hdenPos : (0 : ℚ) < (2 : ℚ) ^ 496 := pow_pos (by norm_num) _
    exact div_nonneg (by norm_num) hdenPos.le
  · have hdenPos : (0 : ℚ) < (2 : ℚ) ^ 496 := pow_pos (by norm_num) _
    rw [div_le_one₀ hdenPos]
    exact one_le_pow₀ (by norm_num)

#print axioms abortProp_iff_some_none
#print axioms eightAbort_card_exact
#print axioms pow_failure_union_bound
#print axioms eightAbortMass_exact
#print axioms eightAbortMass_le_union_bound

end M31RetryOutputFiber
