import SelectedGRSSubmodule
import LinearFactorInterpolation
import PrimeFactorRegularity

/-! A restricted retained-prime-factor class now recovers actual source
message components. Good challenges refer to existence of original-code
messages, not an arbitrary ambient degree-1024 polynomial. Primitivity
derives denominator regularity for every polynomial root. The separate
polynomial-in-gamma rational-root premise is not removed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedLinearFactorRecovery
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.SelectedGRSSubmodule
noncomputable section

theorem linear_root_iff {k : Type*} [Field k]
    (F : TrivariatePolynomial k) (linear : F.natDegree = 1)
    (gamma : k) (U : k[X]) :
    challengeCandidateHom gamma U F = 0 ↔
      LinearFactorInterpolation.LinearRoot (F.coeff 1) (F.coeff 0) gamma U := by
  have value : challengeCandidateHom gamma U F =
      (F.coeff 1).eval (C gamma) * U + (F.coeff 0).eval (C gamma) := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one linear.le]
    simp only [challengeCandidateHom, RingHom.coe_comp, Function.comp_apply,
      specializeChallenge, Polynomial.coe_mapRingHom, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      substituteCandidate, Polynomial.coe_evalRingHom, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  change challengeCandidateHom gamma U F = 0 ↔
    (F.coeff 1).eval (C gamma) * U + (F.coeff 0).eval (C gamma) = 0
  rw [value]

def goodChallenges (F : TrivariatePolynomial K) (Gamma : Finset K) : Finset K := by
  classical
  exact Gamma.filter (fun gamma => ∃ message : Message,
    challengeCandidateHom gamma (exactCircleGRSPolynomial message) F = 0)

theorem goodChallenges_eq (P F : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (linear : F.natDegree = 1) (Gamma : Finset K) :
    goodChallenges F Gamma = LinearFactorInterpolation.goodSet originalCode 1024
      (F.coeff 1) (F.coeff 0) Gamma := by
  classical
  ext gamma
  simp only [goodChallenges, LinearFactorInterpolation.goodSet, Finset.mem_filter]
  apply and_congr_right
  intro gammaMember
  constructor
  · rintro ⟨message, root⟩
    refine ⟨PrimeFactorRegularity.prime_linear_root_regular P F nonzero member linear
      gamma (exactCircleGRSPolynomial message) root, exactCircleGRSPolynomial message,
      (mem_originalCode _).mpr ⟨message, rfl⟩,
      exactCircleGRSPolynomial_degree_le message, ?_⟩
    exact (linear_root_iff F linear gamma _).mp root
  · rintro ⟨regular, U, code, degree, root⟩
    obtain ⟨message, rfl⟩ := (mem_originalCode U).mp code
    exact ⟨message, (linear_root_iff F linear gamma _).mpr root⟩

/-- Geometric nodes and resulting actual components are chosen from the
fixed factor, before any particular actual gamma. Every later polynomial
root is identified, with no regularity or original-code premise on it. -/
theorem actual_message_dichotomy
    (P F : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (linear : F.natDegree = 1)
    (R : Polynomial (FractionRing K[X])) (rootDegree : R.natDegree ≤ 28)
    (equation : (F.coeff 1).map (algebraMap K[X] (FractionRing K[X])) * R +
      (F.coeff 0).map (algebraMap K[X] (FractionRing K[X])) = 0)
    (Gamma : Finset K) :
    (goodChallenges F Gamma).card ≤ 28 ∨
      ∃ messages : Fin 29 → Message,
        (∀ j, R.coeff j.val = algebraMap K[X] (FractionRing K[X])
          (exactCircleGRSPolynomial (messages j))) ∧
        ∀ gamma (U : K[X]), challengeCandidateHom gamma U F = 0 →
          U = exactCircleGRSPolynomial (∑ j : Fin 29, gamma^j.val • messages j) := by
  classical
  rcases LinearFactorInterpolation.rational_29_dichotomy
    (F.coeff 1) (F.coeff 0) R rootDegree equation originalCode Gamma with sparse | dense
  · left
    rw [goodChallenges_eq P F nonzero member linear Gamma]
    exact sparse
  · right
    obtain ⟨p, properties, cover⟩ := dense
    obtain ⟨messages, encoded, unique⟩ := components_lift p (fun j => (properties j).1)
    refine ⟨messages, ?_, ?_⟩
    · intro j
      rw [encoded j]
      exact (properties j).2.2
    · intro gamma U root
      have identified := cover gamma U
        (PrimeFactorRegularity.prime_linear_root_regular P F nonzero member linear gamma U root)
        ((linear_root_iff F linear gamma U).mp root)
      rw [identified, ← encoder_eq, map_sum]
      apply Finset.sum_congr rfl
      intro j memberJ
      rw [map_smul, encoder_eq]
      exact congrArg (fun value : K[X] => gamma^j.val • value) (encoded j).symm

#print axioms linear_root_iff
#print axioms goodChallenges_eq
#print axioms actual_message_dichotomy
end
end AspisV8.SelectedLinearFactorRecovery
