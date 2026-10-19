import M31ActualEightWideSampler
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber

abbrev ActualWideSuccessInput :=
  {xs : EightRetryInputs // ∃ w : WideExactOutput, actualEightWideSampler xs = some w}

theorem actualWideSuccess_iff (xs : EightRetryInputs) :
    (∃ w : WideExactOutput, actualEightWideSampler xs = some w) ↔
      AllEightAccepted xs := by
  constructor
  · rintro ⟨w, hrun⟩
    intro i
    obtain ⟨ys, hall, hys, hout⟩ :=
      (actualEightWideSampler_some_iff xs w).mp hrun
    exact hall i
  · intro hall
    have hreturned := (allEightReturned_iff_accepted xs).mpr hall
    have hcanonical : decodeEight xs =
        some (fun i => canonicalOutput (xs i)) := by
      simp [decodeEight, hreturned]
    have hraw : rawDecodedEight xs = (fun i => canonicalOutput (xs i)) := by
      simp [rawDecodedEight, hcanonical]
    have hdecode : decodeEight xs = some (rawDecodedEight xs) := by
      rw [hraw]
      exact hcanonical
    refine ⟨outputToWideExact (rawDecodedEight xs), ?_⟩
    simp [actualEightWideSampler, hdecode]

def actualWideSuccessInputEquiv : ActualWideSuccessInput ≃ EightSuccessInput where
  toFun x := ⟨x.1, (actualWideSuccess_iff x.1).mp x.2⟩
  invFun x := ⟨x.1, (actualWideSuccess_iff x.1).mpr x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem actualWideSuccessInput_card :
    Nat.card ActualWideSuccessInput = Nat.card EightSuccessInput :=
  Nat.card_congr actualWideSuccessInputEquiv

abbrev ActualWideSamplerInputTape (n : Nat) := Fin n → EightRetryInputs
abbrev ActualWideSamplerOutputTape (n : Nat) := Fin n → WideExactOutput

abbrev ActualWideSamplerSuccessTape (n : Nat) :=
  {xs : ActualWideSamplerInputTape n //
    ∀ i : Fin n, ∃ w : WideExactOutput, actualEightWideSampler (xs i) = some w}

abbrev ActualWideSamplerFiber (n : Nat) (ys : ActualWideSamplerOutputTape n) :=
  {xs : ActualWideSamplerInputTape n //
    ∀ i : Fin n, actualEightWideSampler (xs i) = some (ys i)}

/-- This equivalence records the independence in the input tape itself: every
coordinate is one complete 8-limb retry input. -/
def actualWideSamplerSuccessTapeEquiv (n : Nat) :
    ActualWideSamplerSuccessTape n ≃ ((i : Fin n) → ActualWideSuccessInput) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

def actualWideSamplerFiberEquiv (n : Nat) (ys : ActualWideSamplerOutputTape n) :
    ActualWideSamplerFiber n ys ≃ ((i : Fin n) → actualWideOutputFiber (ys i)) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

theorem actualWideSamplerFiber_card (n : Nat) (ys : ActualWideSamplerOutputTape n) :
    Nat.card (ActualWideSamplerFiber n ys) = limbBaseCount ^ (8 * n) := by
  classical
  calc
    Nat.card (ActualWideSamplerFiber n ys) =
        Nat.card ((i : Fin n) → actualWideOutputFiber (ys i)) :=
      Nat.card_congr (actualWideSamplerFiberEquiv n ys)
    _ = ∏ i : Fin n, Nat.card (actualWideOutputFiber (ys i)) := Nat.card_pi
    _ = ∏ _i : Fin n, limbBaseCount ^ 8 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact actualWideOutputFiber_card (ys i)
    _ = (limbBaseCount ^ 8) ^ n := by simp
    _ = limbBaseCount ^ (8 * n) := by rw [pow_mul]

theorem actualWideSamplerSuccessTape_card (n : Nat) :
    Nat.card (ActualWideSamplerSuccessTape n) =
      (P31 ^ 8 * limbBaseCount ^ 8) ^ n := by
  classical
  calc
    Nat.card (ActualWideSamplerSuccessTape n) =
        Nat.card ((i : Fin n) → ActualWideSuccessInput) :=
      Nat.card_congr (actualWideSamplerSuccessTapeEquiv n)
    _ = ∏ _i : Fin n, Nat.card ActualWideSuccessInput := Nat.card_pi
    _ = ∏ _i : Fin n, (P31 ^ 8 * limbBaseCount ^ 8) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [actualWideSuccessInput_card, eightSuccess_count_eq_P31pow_mul_base]
    _ = (P31 ^ 8 * limbBaseCount ^ 8) ^ n := by simp

theorem actualWideSamplerTape_conditional_uniform (n : Nat)
    (ys : ActualWideSamplerOutputTape n) :
    (Nat.card (ActualWideSamplerFiber n ys) : ℚ) /
      (Nat.card (ActualWideSamplerSuccessTape n) : ℚ) =
        1 / (P31 : ℚ) ^ (8 * n) := by
  rw [actualWideSamplerFiber_card, actualWideSamplerSuccessTape_card]
  have hP : (P31 : ℚ) ≠ 0 := by norm_num [P31]
  have hbase : 0 < limbBaseCount := by
    have h := scalar_success_count_eq_P31_mul_base
    rcases Nat.eq_zero_or_pos limbBaseCount with hz | hp
    · rw [hz] at h
      norm_num [P31] at h
    · exact hp
  have hB : (limbBaseCount : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hbase
  push_cast
  change ((limbBaseCount : ℚ) ^ (8 * n)) /
      (((P31 : ℚ) ^ 8 * (limbBaseCount : ℚ) ^ 8) ^ n) =
    1 / (P31 : ℚ) ^ (8 * n)
  rw [mul_pow, ← pow_mul, ← pow_mul]
  field_simp [hP, hB]
  <;> ring

#print axioms actualWideSuccess_iff
#print axioms actualWideSamplerSuccessTapeEquiv
#print axioms actualWideSamplerFiberEquiv
#print axioms actualWideSamplerFiber_card
#print axioms actualWideSamplerSuccessTape_card
#print axioms actualWideSamplerTape_conditional_uniform

end M31RetryOutputFiber
