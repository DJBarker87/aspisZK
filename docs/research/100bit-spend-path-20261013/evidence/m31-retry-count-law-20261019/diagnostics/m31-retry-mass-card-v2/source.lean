import M31RetryAbortFiber
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

abbrev AnyOutputFiber (o : Option Value) := {xs : RetryWords // output decode31 xs = o}

noncomputable def outputPartitionEquiv :
    RetryWords ≃ (Σ o : Option Value, AnyOutputFiber o) where
  toFun xs := ⟨output decode31 xs, ⟨xs, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨o, xs, hxs⟩
    subst o
    rfl

noncomputable def successMass : Nat :=
  ∑ r : Value, Fintype.card (outputFiber decode31 r)

noncomputable def totalMass : Nat := Fintype.card RetryWords

def r0 : Value := ⟨0, by norm_num [P31]⟩

theorem outputFiber_card_eq_base (r : Value) :
    Fintype.card (outputFiber decode31 r) = Fintype.card (outputFiber decode31 r0) := by
  letI : Fintype (outputFiber decode31 r) := outputFiberFintype decode31 r
  letI : Fintype (outputFiber decode31 r0) := outputFiberFintype decode31 r0
  simpa [outputFiberCard] using outputFiber_card_eq r r0

theorem successMass_eq_value_card_mul_base :
    successMass = Fintype.card Value * Fintype.card (outputFiber decode31 r0) := by
  unfold successMass
  calc
    (∑ r : Value, Fintype.card (outputFiber decode31 r)) =
        ∑ _r : Value, Fintype.card (outputFiber decode31 r0) := by
      apply Finset.sum_congr rfl
      intro r _
      exact outputFiber_card_eq_base r
    _ = Fintype.card Value * Fintype.card (outputFiber decode31 r0) := by simp

theorem output_partition_card :
    totalMass = outputNoneFiberCard + successMass := by
  letI : ∀ o : Option Value, Fintype (AnyOutputFiber o) := by
    intro o
    cases o with
    | none => exact outputNoneFiberFintype
    | some r => exact outputFiberFintype decode31 r
  have hnoneCard : Fintype.card (AnyOutputFiber none) = outputNoneFiberCard := by
    unfold outputNoneFiberCard
    rfl
  have hsomeCard (r : Value) :
      Fintype.card (AnyOutputFiber (some r)) = outputFiberCard decode31 r := by
    unfold outputFiberCard
    rfl
  have hpartition := Fintype.card_congr outputPartitionEquiv
  rw [Fintype.card_sigma, Fintype.sum_option] at hpartition
  unfold totalMass
  rw [hpartition, hnoneCard]
  simp only [hsomeCard, successMass]

theorem totalMass_eq_word_pow : totalMass = (2 ^ 32) ^ 16 := by
  unfold totalMass RetryWords Word
  simp [Fintype.card_fun]

theorem successMass_eq_total_sub_abort : successMass = (2 ^ 32) ^ 16 - 2 ^ 16 := by
  have hpart := output_partition_card
  rw [outputNoneFiberCard_eq, totalMass_eq_word_pow] at hpart
  unfold successMass
  omega

theorem each_output_mass_mul_P31 (r : Value) :
    Fintype.card (outputFiber decode31 r) * P31 = (2 ^ 32) ^ 16 - 2 ^ 16 := by
  have hc := outputFiber_card_eq_base r
  have hm := successMass_eq_total_sub_abort
  rw [successMass_eq_value_card_mul_base] at hm
  unfold successMass at hm
  have hp : Fintype.card Value = P31 := by simp [Value, P31]
  rw [hc, hp]
  omega

#print axioms output_partition_card
#print axioms each_output_mass_mul_P31

end M31RetryOutputFiber
