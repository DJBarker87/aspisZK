import SelectedGammaConstantRecovery

/-! A pre-OOD, pre-gamma mathematical family of actual 29-message tuples.
Sparse challenges are charged once over the fixed positive-Y factor family.
This is a gamma exception union, NOT a union of q22 query probabilities. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.LinearMessageFamily
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.SelectedGRSSubmodule AspisV8.SelectedLinearFactorRecovery
open AspisV8.SelectedGammaConstantRecovery
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def branches (P : TrivariatePolynomial K) : Finset (TrivariatePolynomial K) := by
  classical
  exact (positiveYPrimeFactors P).toFinset

def sparseChallenges (P : TrivariatePolynomial K) (Gamma : Finset K) : Finset K := by
  classical
  exact (branches P).biUnion fun F =>
    if (goodChallenges F Gamma).card ≤ 28 then goodChallenges F Gamma else ∅

theorem sparseChallenges_card (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (Gamma : Finset K) : (sparseChallenges P Gamma).card ≤ P.natDegree * 28 := by
  classical
  have branchBound : (branches P).card ≤ P.natDegree :=
    (Multiset.toFinset_card_le _).trans (positiveYPrimeFactors_card_le_natDegree P nonzero)
  calc
    (sparseChallenges P Gamma).card ≤
        ∑ F ∈ branches P,
          (if (goodChallenges F Gamma).card ≤ 28 then goodChallenges F Gamma else ∅).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _F ∈ branches P, 28 := by
      apply Finset.sum_le_sum
      intro F member
      split_ifs with small
      · exact small
      · simp
    _ = (branches P).card * 28 := by simp
    _ ≤ P.natDegree * 28 := Nat.mul_le_mul_right 28 branchBound

def tuple (F : TrivariatePolynomial K) : Fin 29 → Message :=
  if covered : ∃ messages : Fin 29 → Message, MessageCover F messages then
    Classical.choose covered
  else 0

def family (P : TrivariatePolynomial K) : Finset (Fin 29 → Message) := by
  classical
  exact (branches P).image tuple

theorem family_card (P : TrivariatePolynomial K) (nonzero : P ≠ 0) :
    (family P).card ≤ P.natDegree :=
  Finset.card_image_le.trans <|
    (Multiset.toFinset_card_le _).trans (positiveYPrimeFactors_card_le_natDegree P nonzero)

/-- Only the actual gamma is tested for membership in the sparse set.
The tuple/family is not picked retrospectively from that actual challenge.
The supplied message is the actual candidate; other roots of the same factor
are covered too, without assuming they are in the original code. -/
theorem actual_root_sparse_or_covered (P F : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (linear : F.natDegree = 1) (constant : (F.coeff 1).natDegree = 0)
    (small : (F.coeff 0).natDegree ≤ 28)
    (Gamma : Finset K) (gamma : K) (gammaMember : gamma ∈ Gamma)
    (message : Message) (root : challengeCandidateHom gamma
      (exactCircleGRSPolynomial message) F = 0) :
    gamma ∈ sparseChallenges P Gamma ∨
      ∃ messages ∈ family P, MessageCover F messages := by
  classical
  have branchMember : F ∈ branches P := by
    exact Multiset.mem_toFinset.mpr <|
      (mem_positiveYPrimeFactors P F).mpr ⟨member, by omega⟩
  by_cases sparse : (goodChallenges F Gamma).card ≤ 28
  · left
    apply Finset.mem_biUnion.mpr
    refine ⟨F, branchMember, ?_⟩
    rw [if_pos sparse]
    exact Finset.mem_filter.mpr ⟨gammaMember, message, root⟩
  · right
    have covered := (SelectedGammaConstantRecovery.actual_message_dichotomy
      P F nonzero member linear constant small Gamma).resolve_left sparse
    refine ⟨tuple F, Finset.mem_image.mpr ⟨F, branchMember, rfl⟩, ?_⟩
    simpa only [tuple, dif_pos covered] using Classical.choose_spec covered

#print axioms sparseChallenges_card
#print axioms family_card
#print axioms actual_root_sparse_or_covered
end
end AspisV8.LinearMessageFamily
