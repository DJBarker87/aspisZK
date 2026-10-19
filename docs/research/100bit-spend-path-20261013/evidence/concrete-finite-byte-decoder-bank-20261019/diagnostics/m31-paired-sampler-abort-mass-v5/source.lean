import M31PairedWideSamplerLaw
import M31EightLimbAbortBound
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev ActualPairTapeSuccessProp (n : Nat) (xs : ActualWidePairInputTape n) : Prop :=
  ∀ i : Fin n, ∃ y : WidePairOutput, actualWidePairSampler (xs i) = some y
abbrev ActualPairTapeFailure (n : Nat) :=
  {xs : ActualWidePairInputTape n // ¬ ActualPairTapeSuccessProp n xs}

noncomputable def actualPairTapeFailureMass (n : Nat) : ℚ :=
  (Nat.card (ActualPairTapeFailure n) : ℚ) /
    (Nat.card (ActualWidePairInputTape n) : ℚ)

theorem actualWidePairInputTape_card (n : Nat) :
    Nat.card (ActualWidePairInputTape n) = retryWordTotal ^ (16*n) := by
  classical
  have hpair : Nat.card WidePairInput = retryWordTotal ^ 16 := by
    unfold WidePairInput
    rw [Nat.card_prod, eightRetryInput_card, eightRetryInput_card]
    change (retryWordTotal^8) * (retryWordTotal^8) = retryWordTotal^16
    rw [← pow_two, ← pow_mul]
    norm_num
  calc
    Nat.card (ActualWidePairInputTape n) =
        ∏ _i : Fin n, Nat.card WidePairInput := Nat.card_pi
    _ = (Nat.card WidePairInput)^n := by simp
    _ = retryWordTotal ^ (16*n) := by rw [hpair, ← pow_mul]

theorem actualWidePairSuccessTape_card_as_retry (n : Nat) :
    Nat.card (ActualWidePairSuccessTape n) = retryWordSuccess ^ (16*n) := by
  rw [actualWidePairSuccessTape_card]
  have hbase : P31 * limbBaseCount = retryWordSuccess := by
    symm
    exact scalar_success_count_eq_P31_mul_base
  have hcell : (P31 ^ 8 * limbBaseCount ^ 8)^2 = retryWordSuccess ^ 16 := by
    rw [← Nat.mul_pow, ← hbase, ← pow_mul]
  rw [hcell, pow_mul]

theorem actualPairTapeFailure_card (n : Nat) :
    Nat.card (ActualPairTapeFailure n) =
      retryWordTotal ^ (16*n) - retryWordSuccess ^ (16*n) := by
  classical
  letI : Fintype (ActualWidePairInputTape n) := inferInstance
  letI : Fintype (ActualWidePairSuccessTape n) := inferInstance
  letI : Fintype (ActualPairTapeFailure n) := inferInstance
  have hcard : Fintype.card (ActualPairTapeFailure n) =
      Fintype.card (ActualWidePairInputTape n) -
        Fintype.card (ActualWidePairSuccessTape n) := by
    change Fintype.card {xs : ActualWidePairInputTape n // ¬ ActualPairTapeSuccessProp n xs} =
      Fintype.card (ActualWidePairInputTape n) -
        Fintype.card {xs : ActualWidePairInputTape n // ActualPairTapeSuccessProp n xs}
    exact Fintype.card_subtype_compl _
  have hfail : Nat.card (ActualPairTapeFailure n) = Fintype.card (ActualPairTapeFailure n) :=
    Nat.card_eq_fintype_card
  have hin : Nat.card (ActualWidePairInputTape n) = Fintype.card (ActualWidePairInputTape n) :=
    Nat.card_eq_fintype_card
  have hsucc : Nat.card (ActualWidePairSuccessTape n) = Fintype.card (ActualWidePairSuccessTape n) :=
    Nat.card_eq_fintype_card
  rw [hfail, hcard, ← hin, ← hsucc, actualWidePairInputTape_card,
    actualWidePairSuccessTape_card_as_retry]

theorem actualPairTape_abort_mass_exact (n : Nat) :
    actualPairTapeFailureMass n =
      1 - (1 - (1 : ℚ) / (2 : ℚ)^496)^(16*n) := by
  unfold actualPairTapeFailureMass
  rw [actualPairTapeFailure_card, actualWidePairInputTape_card]
  have hS : retryWordSuccess ≤ retryWordTotal := retryWordSuccess_le_total
  have hSn : retryWordSuccess^(16*n) ≤ retryWordTotal^(16*n) :=
    Nat.pow_le_pow_left hS (16*n)
  have hTpos : (retryWordTotal : ℚ) ≠ 0 := by
    rw [retryWordTotal_cast_factor]
    exact mul_ne_zero (pow_ne_zero 16 (by norm_num)) (pow_ne_zero 496 (by norm_num))
  have hratio := nat_pow_sub_ratio retryWordSuccess retryWordTotal (16*n) hS hTpos
  have hsingle : (retryWordSuccess : ℚ)/(retryWordTotal : ℚ) =
      1 - (1 : ℚ)/(2 : ℚ)^496 := by
    rw [retryWordSuccess_cast, retryWordTotal_cast_factor]
    have hp : (2 : ℚ)^496 ≠ 0 := pow_ne_zero 496 (by norm_num)
    field_simp [hp]
    <;> ring
  calc
    ((retryWordTotal^(16*n) - retryWordSuccess^(16*n) : Nat) : ℚ) /
      ((retryWordTotal^(16*n) : Nat) : ℚ) =
        1 - ((retryWordSuccess : ℚ)/(retryWordTotal : ℚ))^(16*n) := hratio
    _ = 1 - (1 - (1 : ℚ)/(2 : ℚ)^496)^(16*n) := by rw [hsingle]

theorem actualPairTape_abort_mass_le_union (n : Nat) :
    actualPairTapeFailureMass n ≤ (16*n : ℚ) * ((1 : ℚ)/(2 : ℚ)^496) := by
  rw [actualPairTape_abort_mass_exact]
  push_cast
  apply pow_failure_union_bound
  · have hp : (0 : ℚ) < (2 : ℚ)^496 := pow_pos (by norm_num) _
    exact div_nonneg (by norm_num) hp.le
  · have hp : (0 : ℚ) < (2 : ℚ)^496 := pow_pos (by norm_num) _
    rw [div_le_one₀ hp]
    exact one_le_pow₀ (by norm_num)

#print axioms actualWidePairInputTape_card
#print axioms actualWidePairSuccessTape_card_as_retry
#print axioms actualPairTapeFailure_card
#print axioms actualPairTape_abort_mass_exact
#print axioms actualPairTape_abort_mass_le_union

end M31RetryOutputFiber
