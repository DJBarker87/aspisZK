import M31EightLimbSuccessCount
import M31RetryOutputMassNat
import M31RetryMassRational
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

noncomputable def limbBaseCount : Nat := Nat.card (AnyOutputFiber (some r0))

def eightConditionalMass (ys : EightValues) : ℚ :=
  (Nat.card (eightOutputFiber ys) : ℚ) / (Nat.card EightSuccessInput : ℚ)

theorem outputFiberNatCard_eq_base (r : Value) :
    Nat.card (outputFiber decode31 r) = limbBaseCount := by
  have hnat : Nat.card (outputFiber decode31 r) = outputFiberCard decode31 r := by
    letI : Fintype (outputFiber decode31 r) := outputFiberFintype decode31 r
    change Nat.card (outputFiber decode31 r) =
      @Fintype.card (outputFiber decode31 r) (outputFiberFintype decode31 r)
    exact Nat.card_eq_fintype_card
  rw [hnat, ← natFiberCard_eq_outputFiberCard r,
      natOutputFiber_card_eq_base r]
  rfl

theorem eightOutputFiber_card_limbBase (ys : EightValues) :
    Nat.card (eightOutputFiber ys) = limbBaseCount ^ 8 := by
  calc
    Nat.card (eightOutputFiber ys) = eightOutputFiberCard ys := rfl
    _ = ∏ i : Fin 8, outputFiberCard decode31 (ys i) :=
      eightOutputFiberCard_eq_prod ys
    _ = ∏ _i : Fin 8, limbBaseCount := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← outputFiberNatCard_eq_base (ys i)]
      rfl
    _ = limbBaseCount ^ 8 := by simp [limbBaseCount]

theorem scalar_success_count_eq_P31_mul_base :
    (2 ^ 32) ^ 16 - 2 ^ 16 = P31 * limbBaseCount := by
  have h := (natEachOutputCard_mul_P31 r0).symm
  calc
    (2 ^ 32) ^ 16 - 2 ^ 16 = Nat.card (AnyOutputFiber (some r0)) * P31 := h
    _ = limbBaseCount * P31 := by rfl
    _ = P31 * limbBaseCount := Nat.mul_comm _ _

theorem eightSuccess_count_eq_P31pow_mul_base :
    Nat.card EightSuccessInput = P31 ^ 8 * limbBaseCount ^ 8 := by
  calc
    Nat.card EightSuccessInput = ((2 ^ 32) ^ 16 - 2 ^ 16) ^ 8 :=
      eightSuccessInput_card_exact
    _ = (P31 * limbBaseCount) ^ 8 := by rw [scalar_success_count_eq_P31_mul_base]
    _ = P31 ^ 8 * limbBaseCount ^ 8 := by rw [Nat.mul_pow]

private theorem limbBaseCount_pos : 0 < limbBaseCount := by
  unfold limbBaseCount
  have hprod := natEachOutputCard_mul_P31 r0
  have hsuccess : 0 < (2 ^ 32) ^ 16 - 2 ^ 16 := by norm_num
  rcases Nat.eq_zero_or_pos (Nat.card (AnyOutputFiber (some r0))) with hz | hp
  · rw [hz] at hprod
    simp at hprod
    omega
  · exact hp

theorem eightConditionalMass_uniform (ys : EightValues) :
    eightConditionalMass ys = 1 / (P31 : ℚ) ^ 8 := by
  unfold eightConditionalMass
  rw [eightOutputFiber_card_limbBase, eightSuccess_count_eq_P31pow_mul_base]
  have hP : (P31 : ℚ) ≠ 0 := by norm_num [P31]
  have hB : (limbBaseCount : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt limbBaseCount_pos)
  push_cast
  field_simp [hP, hB]
  <;> ring

#print axioms outputFiberNatCard_eq_base
#print axioms eightOutputFiber_card_limbBase
#print axioms scalar_success_count_eq_P31_mul_base
#print axioms eightSuccess_count_eq_P31pow_mul_base
#print axioms eightConditionalMass_uniform

end M31RetryOutputFiber
