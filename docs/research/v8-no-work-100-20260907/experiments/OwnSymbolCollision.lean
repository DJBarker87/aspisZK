import FixedTargetQuerySupport

/-! A fixed received/component tuple determines its own support and a
pre-gamma exceptional set. Agreement beyond that own support forces a
nonzero scalar-power residual root. No codeword, provider, decoder or
received-word polynomiality is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 180000

namespace AspisV8.OwnSymbolCollision
open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability
noncomputable section
variable {K I : Type*} [Field K]

def residual (received expected : Fin 29 → I → K) (i : I) : K[X] :=
  monomialPolynomial (fun lane => received lane i - expected lane i)

theorem residual_coeff (received expected : Fin 29 → I → K) (i : I) (lane : Fin 29) :
    (residual received expected i).coeff lane.val = received lane i - expected lane i :=
  monomialPolynomial_coeff _ lane

theorem residual_degree (received expected : Fin 29 → I → K) (i : I) :
    (residual received expected i).natDegree ≤ 28 :=
  monomialPolynomial_natDegree_le (by decide) _

theorem residual_zero_iff (received expected : Fin 29 → I → K) (i : I) :
    residual received expected i = 0 ↔ ∀ lane, received lane i = expected lane i := by
  constructor
  · intro zero lane
    have coefficient := congrArg (fun P : K[X] => P.coeff lane.val) zero
    rw [residual_coeff, Polynomial.coeff_zero, sub_eq_zero] at coefficient
    exact coefficient
  · intro equal
    have values : (fun lane => received lane i - expected lane i) = (0 : Fin 29 → K) := by
      funext lane
      exact sub_eq_zero.mpr (equal lane)
    change monomialPolynomial (fun lane => received lane i - expected lane i) = 0
    rw [values]
    simp only [monomialPolynomial, Pi.zero_apply, Polynomial.C_0,
      zero_mul, Finset.sum_const_zero]

theorem residual_eval (received expected : Fin 29 → I → K) (i : I) (gamma : K) :
    (residual received expected i).eval gamma =
      (∑ lane : Fin 29, gamma^lane.val * received lane i) -
      (∑ lane : Fin 29, gamma^lane.val * expected lane i) := by
  simp only [residual, monomialPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro lane member
  ring

variable [DecidableEq I]

def own (U : Finset I) (received expected : Fin 29 → I → K) : Finset I := by
  classical
  exact U.filter fun i => ∀ lane, received lane i = expected lane i

def matching (U : Finset I) (received expected : Fin 29 → I → K) (gamma : K) : Finset I := by
  classical
  exact U.filter fun i => (residual received expected i).eval gamma = 0

def exception (U : Finset I) (received expected : Fin 29 → I → K)
    (Gamma : Finset K) : Finset K := by
  classical
  exact (U \ own U received expected).biUnion fun i =>
    Gamma.filter fun gamma => (residual received expected i).eval gamma = 0

theorem exception_subset (U : Finset I) (received expected : Fin 29 → I → K)
    (Gamma : Finset K) : exception U received expected Gamma ⊆ Gamma := by
  classical
  intro gamma member
  obtain ⟨i, outside, root⟩ := Finset.mem_biUnion.mp member
  exact (Finset.mem_filter.mp root).1

theorem exception_card (U : Finset I) (received expected : Fin 29 → I → K)
    (Gamma : Finset K) :
    (exception U received expected Gamma).card ≤ 28*(U.card - (own U received expected).card) := by
  classical
  have ownSubset : own U received expected ⊆ U := Finset.filter_subset _ _
  calc
    (exception U received expected Gamma).card ≤
        ∑ i ∈ U \ own U received expected,
          (Gamma.filter fun gamma => (residual received expected i).eval gamma = 0).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ U \ own U received expected, 28 := by
      apply Finset.sum_le_sum
      intro i outside
      have nonzero : residual received expected i ≠ 0 := by
        intro zero
        apply (Finset.mem_sdiff.mp outside).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp outside).1,
          (residual_zero_iff received expected i).mp zero⟩
      exact FixedTargetQuerySupport.root_filter_card_le Gamma _ nonzero 28
        (residual_degree received expected i)
    _ = _ := by simp [Finset.card_sdiff_of_subset ownSubset, Nat.mul_comm]

/-- The count condition supplies an actual outside symbol, not an assumed
candidate-family member. The exception is fixed before the actual gamma. -/
theorem excess_matching_mem_exception (U : Finset I)
    (received expected : Fin 29 → I → K) (Gamma : Finset K) (gamma : K)
    (gammaMember : gamma ∈ Gamma)
    (excess : (own U received expected).card < (matching U received expected gamma).card) :
    gamma ∈ exception U received expected Gamma := by
  classical
  have notSubset : ¬ matching U received expected gamma ⊆ own U received expected := by
    intro subset
    exact Nat.not_lt_of_ge (Finset.card_le_card subset) excess
  obtain ⟨i, matched, outside⟩ := Finset.not_subset.mp notSubset
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp matched).1, outside⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨gammaMember, (Finset.mem_filter.mp matched).2⟩

#print axioms residual_coeff
#print axioms residual_degree
#print axioms residual_zero_iff
#print axioms residual_eval
#print axioms exception_subset
#print axioms exception_card
#print axioms excess_matching_mem_exception
end
end AspisV8.OwnSymbolCollision
