import M31RetryFiberUniformNat

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

theorem natOutputMass_eq_P_mul_base :
    natOutputMass = P31 * Nat.card (AnyOutputFiber (some r0)) := by
  unfold natOutputMass
  calc
    (∑ r : Value, Nat.card (AnyOutputFiber (some r))) =
        ∑ _r : Value, Nat.card (AnyOutputFiber (some r0)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact natOutputFiber_card_eq_base r
    _ = Fintype.card Value * Nat.card (AnyOutputFiber (some r0)) := by
      change (Finset.univ.sum fun _ : Value => Nat.card (AnyOutputFiber (some r0))) = _
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = P31 * Nat.card (AnyOutputFiber (some r0)) := by
      rw [Fintype.card_fin]

theorem natEachOutputCard_mul_P31 (r : Value) :
    Nat.card (AnyOutputFiber (some r)) * P31 = (2 ^ 32) ^ 16 - 2 ^ 16 := by
  calc
    Nat.card (AnyOutputFiber (some r)) * P31 =
        P31 * Nat.card (AnyOutputFiber (some r0)) := by
      rw [natOutputFiber_card_eq_base r]
      exact Nat.mul_comm _ _
    _ = natOutputMass := natOutputMass_eq_P_mul_base.symm
    _ = (2 ^ 32) ^ 16 - 2 ^ 16 := natOutputMass_eq_success_count

#print axioms natOutputMass_eq_P_mul_base
#print axioms natEachOutputCard_mul_P31

end M31RetryOutputFiber
