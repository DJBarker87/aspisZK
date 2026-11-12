import R0.Fold
import R0.ResponseSelection
import Wide.JointList
import Wide.MatchedInstances

/-! The lists and the existential unmatched-response sets in §5, steps
1, 2 and 6. Tuples are represented by their unique exact messages. -/
set_option autoImplicit false
namespace AspisR0.ListsResponses
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisWide.JointList AspisWide.MultiplicityThreeGS
open AspisV5FriCoherentCandidateExtraction AspisV6Width29CorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisWide.DegreeThreeMatched AspisWide.MatchedInstances
open AspisV6PublishedTheoremInterfaces
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def Close (f : InitialWord K) : Finset (InitialMessage K) := by
  classical
  exact Finset.univ.filter fun q => 38230 ≤ (agreementSet f (exactInitialEncoder q)).card

def Lambda (W : Fin 29 → InitialWord K) : Finset (Fin 29 → InitialMessage K) := by
  classical
  exact Finset.univ.filter fun t => 38230 ≤ (width29JointAgreementSet exactInitialEncoder W t).card

/-- The literal codeword-tuple version of Lambda. -/
def LambdaCodewords (W : Fin 29 → InitialWord K) : Finset (Fin 29 → InitialWord K) := by
  classical
  exact (Lambda W).image (fun t l => exactInitialEncoder (t l))

def LambdaR (R : Fin 29 → InitialWord K) := Lambda R

-- X6b scratch (tool, nothing proved): sorry only in this scratch file.
-- c1: state after the simp only of the carried step, explicit instances
set_option pp.explicit true in
theorem c1 (f : InitialWord K) : (Close f).card ≤ 100 := by
  classical
  letI : Fintype (ExactInitialCloseCandidate f) := Fintype.ofFinite _
  have hb : Fintype.card (ExactInitialCloseCandidate f) < 101 := by
    simpa only [Nat.card_eq_fintype_card] using exactInitialCloseCandidate_card_lt_101 f
  rw [Fintype.card_subtype] at hb
  have hc : (Close f).card < 101 := by
    simp only [Close, closeAtLeast, agreementCount, agreementSet] at hb ⊢
    trace_state
    sorry
  omega

-- c2: carried step with the filter instances normalised (Finset.filter_congr_decidable)
theorem c2 (f : InitialWord K) : (Close f).card ≤ 100 := by
  classical
  letI : Fintype (ExactInitialCloseCandidate f) := Fintype.ofFinite _
  have hb : Fintype.card (ExactInitialCloseCandidate f) < 101 := by
    simpa only [Nat.card_eq_fintype_card] using exactInitialCloseCandidate_card_lt_101 f
  rw [Fintype.card_subtype] at hb
  have hc : (Close f).card < 101 := by
    simpa only [Close, closeAtLeast, agreementCount, agreementSet,
      Finset.filter_congr_decidable] using hb
  omega

end
end AspisR0.ListsResponses
