import M31RetryAbortFiber
import Mathlib.SetTheory.Cardinal.Finite
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

noncomputable def natOutputMass : Nat :=
  ∑ r : Value, Nat.card (AnyOutputFiber (some r))

noncomputable def natTotalMass : Nat := Nat.card RetryWords

noncomputable def natNoneMass : Nat := Nat.card (AnyOutputFiber none)

theorem output_partition_nat_card :
    natTotalMass = natNoneMass + natOutputMass := by
  unfold natTotalMass natNoneMass natOutputMass
  calc
    Nat.card RetryWords = Nat.card (Σ o : Option Value, AnyOutputFiber o) :=
      Nat.card_congr outputPartitionEquiv
    _ = ∑ o : Option Value, Nat.card (AnyOutputFiber o) := Nat.card_sigma
    _ = Nat.card (AnyOutputFiber none) +
        ∑ r : Value, Nat.card (AnyOutputFiber (some r)) := by
      rw [Fintype.sum_option]

theorem natTotalMass_eq_word_pow : natTotalMass = (2 ^ 32) ^ 16 := by
  unfold natTotalMass RetryWords Word
  simp

theorem natNoneMass_eq_abort : natNoneMass = 2 ^ 16 := by
  unfold natNoneMass AnyOutputFiber
  letI : Fintype OutputNoneFiber := outputNoneFiberFintype
  have h := outputNoneFiberCard_eq
  simpa [outputNoneFiberCard, Nat.card_eq_fintype_card] using h

theorem natOutputMass_eq_success_count :
    natOutputMass = (2 ^ 32) ^ 16 - 2 ^ 16 := by
  have h := output_partition_nat_card
  rw [natTotalMass_eq_word_pow, natNoneMass_eq_abort] at h
  have hsum : 2 ^ 16 + natOutputMass = (2 ^ 32) ^ 16 := h.symm
  calc
    natOutputMass = (2 ^ 16 + natOutputMass) - 2 ^ 16 := by
      exact (Nat.add_sub_cancel_left (2 ^ 16) natOutputMass).symm
    _ = (2 ^ 32) ^ 16 - 2 ^ 16 := by rw [hsum]

#print axioms output_partition_nat_card
#print axioms natTotalMass_eq_word_pow
#print axioms natNoneMass_eq_abort
#print axioms natOutputMass_eq_success_count

end M31RetryOutputFiber
