import MiddleSimpleRootV7
import SelectedLinearCover

/-! Generic selected-message classification for any small linear-Y parent.
The parent is a parameter fixed before OOD; its actual source selection and
support-root bridge live in SelectedMiddleSimpleParent. One gamma exception
accounts for content, zero specialization and non-retained factors together.
The non-small linear obstruction is a separate pre-OOD two-point event.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.MiddleLinearClassification
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.FactorIdentityCover AspisV8.LinearDenominatorFactors
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Message := SelectedGRSSubmodule.Message

theorem pair_obstruction_budget (P : TrivariatePolynomial K)
    (weight : trivariateYZWeight 28 P ≤ 40)
    (xDegree : (trivariateXOuterEquiv K P).natDegree ≤ 803229) :
    (2*trivariateYZWeight 28 P+1)*(trivariateXOuterEquiv K P).natDegree ≤ 65061549 := by
  calc
    _ ≤ (2*40+1)*803229 := Nat.mul_le_mul
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 weight) 1) xDegree
    _ = _ := by norm_num

/-- The at-most-one tuple is selected from P, not from the actual gamma.
There is no earlyC1 premise, own-support inference or provider assumption.
Points and answers may be chosen sequentially; E is fixed before both. -/
theorem exists_classification (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (yDegree : P.natDegree ≤ 1)
    (xDegree : (trivariateXOuterEquiv K P).natDegree ≤ 803229)
    (weight : trivariateYZWeight 28 P ≤ 40) (Gamma : Finset K) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 65061549 ∧
      (LinearMessageFamily.family P).card ≤ 1 ∧
      (LinearMessageFamily.sparseChallenges P Gamma).card ≤ 28 ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
        (∀ r, (answers r).natDegree ≤ 28) →
        ∃ beta : K[X], beta ≠ 0 ∧ beta.natDegree ≤ 40 ∧
          ∀ (gamma : K) (message : Message), gamma ∈ Gamma →
            challengeCandidateHom gamma (exactCircleGRSPolynomial message) P = 0 →
            (∀ r, (exactCircleGRSPolynomial message).eval (points r) =
              (answers r).eval gamma) →
            beta.eval gamma = 0 ∨ (∀ r, E.eval (points r) = 0) ∨
              gamma ∈ LinearMessageFamily.sparseChallenges P Gamma ∨
              ∃ messages ∈ LinearMessageFamily.family P,
                message = ClaimTransport.batch gamma messages := by
  obtain ⟨E, eNonzero, eDegree, control⟩ := exists_parent_obstruction 28 P nonzero
  have familyCard := (LinearMessageFamily.family_card P nonzero).trans yDegree
  have sparseCard : (LinearMessageFamily.sparseChallenges P Gamma).card ≤ 28 :=
    (LinearMessageFamily.sparseChallenges_card P nonzero Gamma).trans
      (by simpa using Nat.mul_le_mul_right 28 yDegree)
  refine ⟨E, eNonzero, eDegree.trans (pair_obstruction_budget P weight xDegree),
    familyCard, sparseCard, ?_⟩
  intro points answers answerDegrees
  obtain ⟨beta, betaNonzero, betaDegree, cover⟩ :=
    exists_identity_factor_cover 28 P nonzero points answers answerDegrees
  refine ⟨beta, betaNonzero, betaDegree.trans weight, ?_⟩
  intro gamma message inGamma root pointValues
  rcases cover gamma (exactCircleGRSPolynomial message) root pointValues with hit | retainedRoot
  · exact Or.inl hit
  · obtain ⟨F, member, retained, candidate⟩ := retainedRoot
    have linear : F.natDegree = 1 :=
      MiddleSimpleRoot.positive_factor_linear_of_parent P F nonzero yDegree member retained.1
    rcases control points answers F member linear retained answerDegrees with small | hit
    · rcases SelectedLinearCover.small_root_message_cover P F nonzero member linear small
        Gamma gamma inGamma message candidate with sparse | covered
      · exact Or.inr (Or.inr (Or.inl sparse))
      · obtain ⟨messages, member, equality⟩ := covered
        refine Or.inr (Or.inr (Or.inr ⟨messages, member, ?_⟩))
        simpa only [ClaimTransport.batch] using equality
    · exact Or.inr (Or.inl hit)

#print axioms pair_obstruction_budget
#print axioms exists_classification
end
end AspisV8.MiddleLinearClassification
