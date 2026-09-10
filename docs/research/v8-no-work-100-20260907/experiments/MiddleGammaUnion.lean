import EarlyC1HigherYSupport

/-! Finite gamma closure after the auxiliary linear-parent source adapter.
The original higher-Y parent is kept, and a fixed family of at most one
curve is counted against all its prime factors additively. The shared and
sparse exceptions may overlap. The OOD pair-root alternative is not averaged.
No early decoder, regularity, own-support, sampler or independence premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.MiddleGammaUnion
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.EarlyC1HigherYSupport.Generic
noncomputable section
variable {K I : Type*} [Field K]

/-- I can be the actual message-tuple type; no finite universe of tuples is
enumerated. The supplied finite family is fixed before the charged gamma. -/
def familyHits (P : TrivariatePolynomial K) (curve : I → Polynomial K[X])
    (family : Finset I) (Gamma : Finset K) : Finset K := by
  classical
  exact family.biUnion fun p => coherentHits (curvePrimeFactors P) (curve p) Gamma

theorem mem_familyHits (P : TrivariatePolynomial K) (curve : I → Polynomial K[X])
    (family : Finset I) (Gamma : Finset K) (gamma : K) :
    gamma ∈ familyHits P curve family Gamma ↔
      ∃ p ∈ family, gamma ∈ coherentHits (curvePrimeFactors P) (curve p) Gamma := by
  classical
  simp only [familyHits, Finset.mem_biUnion]

/-- The old parent's additive factor-weight theorem is reused. Neither
distinct factors nor disjoint coherent sets are assumed. -/
theorem coherent_family_count (degree : Nat) (P : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (curve : I → Polynomial K[X]) (family : Finset I)
    (small : ∀ p ∈ family, (curve p).natDegree ≤ degree) (Gamma : Finset K) :
    (familyHits P curve family Gamma).card ≤
      family.card * trivariateYZWeight degree P := by
  classical
  unfold familyHits
  apply Finset.card_biUnion_le_card_mul
  intro p member
  exact coherent_parent_count degree P nonzero (curve p) (small p member) Gamma

/-- An explicit union bound, not an assertion that the three cases are
disjoint. All later-history/adaptive choices are allowed inside capture. -/
theorem captured_union_card (degree : Nat) (P : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (curve : I → Polynomial K[X]) (family : Finset I)
    (small : ∀ p ∈ family, (curve p).natDegree ≤ degree)
    (Gamma hit shared sparse : Finset K)
    (capture : ∀ gamma ∈ hit,
      gamma ∈ shared ∨ gamma ∈ sparse ∨
        ∃ p ∈ family, gamma ∈ coherentHits (curvePrimeFactors P) (curve p) Gamma) :
    hit.card ≤ shared.card + sparse.card +
      family.card * trivariateYZWeight degree P := by
  classical
  have inclusion : hit ⊆ shared ∪ (sparse ∪ familyHits P curve family Gamma) := by
    intro gamma member
    rcases capture gamma member with first | second | covered
    · exact Finset.mem_union_left _ first
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ second)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        ((mem_familyHits P curve family Gamma gamma).mpr covered))
  have bound := Finset.card_le_card inclusion
  have outer := Finset.card_union_le shared (sparse ∪ familyHits P curve family Gamma)
  have inner := Finset.card_union_le sparse (familyHits P curve family Gamma)
  have coherent := coherent_family_count degree P nonzero curve family small Gamma
  omega

/-- Exact 40+28+117077 closure. The family bound is at most one, not an
unpaid union over all possible reconstructed tuples or higher-Y factors. -/
theorem middle_card (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (weight : trivariateYZWeight 28 P ≤ 117077)
    (curve : I → Polynomial K[X]) (family : Finset I)
    (one : family.card ≤ 1) (small : ∀ p ∈ family, (curve p).natDegree ≤ 28)
    (Gamma hit shared sparse : Finset K)
    (sharedSmall : shared.card ≤ 40) (sparseSmall : sparse.card ≤ 28)
    (capture : ∀ gamma ∈ hit,
      gamma ∈ shared ∨ gamma ∈ sparse ∨
        ∃ p ∈ family, gamma ∈ coherentHits (curvePrimeFactors P) (curve p) Gamma) :
    hit.card ≤ 117145 := by
  have bound := captured_union_card 28 P nonzero curve family small Gamma hit shared sparse capture
  have product : family.card * trivariateYZWeight 28 P ≤ 117077 := by
    calc
      family.card * trivariateYZWeight 28 P ≤ 1 * 117077 := Nat.mul_le_mul one weight
      _ = 117077 := Nat.one_mul _
  omega

/-- The polynomial obstruction is fixed outside this finite union argument.
This theorem assigns it no sampler law and does not condition Gamma on it. -/
theorem pair_root_or_middle_card (E : K[X]) (points : Fin 2 → K)
    (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (weight : trivariateYZWeight 28 P ≤ 117077)
    (curve : I → Polynomial K[X]) (family : Finset I)
    (one : family.card ≤ 1) (small : ∀ p ∈ family, (curve p).natDegree ≤ 28)
    (Gamma hit shared sparse : Finset K)
    (sharedSmall : shared.card ≤ 40) (sparseSmall : sparse.card ≤ 28)
    (capture : ¬ (E.eval (points 0) = 0 ∧ E.eval (points 1) = 0) →
      ∀ gamma ∈ hit,
        gamma ∈ shared ∨ gamma ∈ sparse ∨
          ∃ p ∈ family, gamma ∈ coherentHits (curvePrimeFactors P) (curve p) Gamma) :
    (E.eval (points 0) = 0 ∧ E.eval (points 1) = 0) ∨ hit.card ≤ 117145 := by
  classical
  by_cases pairRoot : E.eval (points 0) = 0 ∧ E.eval (points 1) = 0
  · exact Or.inl pairRoot
  · exact Or.inr (middle_card P nonzero weight curve family one small
      Gamma hit shared sparse sharedSmall sparseSmall (capture pairRoot))

#print axioms mem_familyHits
#print axioms coherent_family_count
#print axioms captured_union_card
#print axioms middle_card
#print axioms pair_root_or_middle_card
end
end AspisV8.MiddleGammaUnion
