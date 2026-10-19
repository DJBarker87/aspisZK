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

@[simp] theorem mem_Close (f : InitialWord K) (q : InitialMessage K) :
    q ∈ Close f ↔ 38230 ≤ (agreementSet f (exactInitialEncoder q)).card := by simp [Close]
@[simp] theorem mem_Lambda (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K) :
    t ∈ Lambda W ↔ 38230 ≤ (width29JointAgreementSet exactInitialEncoder W t).card := by simp [Lambda]

theorem Close_card (f : InitialWord K) : (Close f).card ≤ 100 := by
  classical
  letI : Fintype (ExactInitialCloseCandidate f) := Fintype.ofFinite _
  have hb : Fintype.card (ExactInitialCloseCandidate f) < 101 := by
    simpa only [Nat.card_eq_fintype_card] using exactInitialCloseCandidate_card_lt_101 f
  rw [Fintype.card_subtype] at hb
  have hc : (Close f).card < 101 := by
    simpa only [Close, closeAtLeast, agreementCount, agreementSet] using hb
  omega

theorem Lambda_card (W : Fin 29 → InitialWord K) : (Lambda W).card ≤ 100 := by
  classical
  generalize hfamily : Lambda W = family
  apply jointInitialList_card_le_100 W family
  intro t ht
  rw [← hfamily, mem_Lambda] at ht
  exact ht

theorem LambdaR_card (R : Fin 29 → InitialWord K) : (LambdaR R).card ≤ 100 := Lambda_card R

theorem LambdaCodewords_card (W : Fin 29 → InitialWord K) : (LambdaCodewords W).card ≤ 100 := by
  classical
  exact (Finset.card_image_le).trans (Lambda_card W)

abbrev InitialResponse (K : Type) := InitialMessage K × Finset (Fin 1048576)
abbrev FinalResponse (K : Type) := FinalMessage K × Finset (Fin 262144)

def initialConstant (r : InitialResponse K) : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K) :=
  ⟨fun _ => r.1, fun _ => r.2⟩
def finalConstant (r : FinalResponse K) : ProximateStrategy K (Fin 262144) (FinalMessage K) :=
  ⟨fun _ => r.1, fun _ => r.2⟩

def GammaValid (R : Fin 29 → InitialWord K) (gamma : K) (r : InitialResponse K) : Prop :=
  Width29ValidResponse exactInitialEncoder 38229 R (initialConstant r) gamma
def GammaMatched (R : Fin 29 → InitialWord K) (gamma : K) (r : InitialResponse K) : Prop :=
  HasMatchingWidth29Decomposition exactInitialEncoder R (initialConstant r) gamma

def AlphaValid (g : Fin 4 → FinalWord K) (alpha : K) (r : FinalResponse K) : Prop :=
  ValidResponse exactFinalEncoder 9557 g (finalConstant r) alpha
def AlphaMatched (g : Fin 4 → FinalWord K) (alpha : K) (r : FinalResponse K) : Prop :=
  HasMatchingDecomposition exactFinalEncoder g (finalConstant r) alpha

theorem gamma_matched_iff (R : Fin 29 → InitialWord K) (gamma : K) (r : InitialResponse K) :
    GammaMatched R gamma r ↔ ∃ t : Fin 29 → InitialMessage K,
      r.2 ⊆ width29JointAgreementSet exactInitialEncoder R t ∧ r.1 = exactInitialMessageCurve t gamma := by
  constructor
  · rintro ⟨t,hs,hc⟩
    exact ⟨t,hs,exactInitialEncoder_injective (hc.trans (exactInitialEncoder_messageCurve t gamma).symm)⟩
  · rintro ⟨t,hs,hc⟩
    refine ⟨t,hs,?_⟩
    change exactInitialEncoder r.1 = _
    rw [hc, exactInitialEncoder_messageCurve]

def GammaBad (R : Fin 29 → InitialWord K) (gamma : K) (r : InitialResponse K) : Prop :=
  GammaValid R gamma r ∧ ¬ GammaMatched R gamma r
def AlphaBad (g : Fin 4 → FinalWord K) (alpha : K) (r : FinalResponse K) : Prop :=
  AlphaValid g alpha r ∧ ¬ AlphaMatched g alpha r

def B1 (R : Fin 29 → InitialWord K) : Finset K := by
  classical
  exact Finset.univ.filter fun gamma => gamma ≠ 0 ∧ ∃ r, GammaBad R gamma r

def B6 (g : Fin 4 → FinalWord K) : Finset K := by
  classical
  exact Finset.univ.filter fun alpha => ∃ r, AlphaBad g alpha r

@[simp] theorem mem_B1 (R : Fin 29 → InitialWord K) (gamma : K) :
    gamma ∈ B1 R ↔ gamma ≠ 0 ∧ ∃ r, GammaBad R gamma r := by simp [B1]
@[simp] theorem mem_B6 (g : Fin 4 → FinalWord K) (alpha : K) :
    alpha ∈ B6 g ↔ ∃ r, AlphaBad g alpha r := by simp [B6]

theorem B1_card (R : Fin 29 → InitialWord K) : (B1 R).card ≤ 336869026605739 := by
  classical
  letI : Inhabited (InitialResponse K) := ⟨(0,∅)⟩
  let response := ResponseSelection.selected (GammaBad R)
  let strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K) :=
    ⟨fun z => (response z).1,fun z => (response z).2⟩
  have subset : B1 R ⊆ width29GoodChallenges exactInitialEncoder 38229 R
      (width29BadStrategy exactInitialEncoder 38229 R strategy) := by
    intro z hz
    obtain ⟨hnz, hex⟩ := (mem_B1 R z).mp hz
    apply (mem_width29BadStrategy_good_iff _ _ _ _ _).mpr
    exact ⟨hnz, ResponseSelection.selected_spec (GammaBad R) z hex⟩
  exact (Finset.card_le_card subset).trans
    (width29_bad_response_challenges_card_le exactInitialEncoder 38229 initialBatchChallengeCap
      AspisWide.Terminal.exactV7InitialWidth29CurveDecodable R strategy)

theorem B6_card (g : Fin 4 → FinalWord K) : (B6 g).card ≤ 9396508281246 := by
  classical
  letI : Inhabited (FinalResponse K) := ⟨(0,∅)⟩
  let response := ResponseSelection.selected (AlphaBad g)
  let strategy : ProximateStrategy K (Fin 262144) (FinalMessage K) :=
    ⟨fun z => (response z).1,fun z => (response z).2⟩
  have subset : B6 g ⊆ goodChallenges exactFinalEncoder 9557 g
      (badStrategy exactFinalEncoder 9557 g strategy) := by
    intro z hz
    apply (mem_badStrategy_good_iff _ _ _ _ _).mpr
    exact ResponseSelection.selected_spec (AlphaBad g) z ((mem_B6 g z).mp hz)
  exact (Finset.card_le_card subset).trans (exactFinal_bad_response_challenges_card_le g strategy)

theorem gamma_match (R : Fin 29 → InitialWord K) (gamma : K) (hnz : gamma ≠ 0)
    (hgood : gamma ∉ B1 R) (r : InitialResponse K) (hv : GammaValid R gamma r) :
    ∃ t ∈ LambdaR R, r.2 ⊆ width29JointAgreementSet exactInitialEncoder R t ∧
      r.1 = exactInitialMessageCurve t gamma := by
  have hm : GammaMatched R gamma r := by
    by_contra hm
    exact hgood ((mem_B1 R gamma).mpr ⟨hnz,r,hv,hm⟩)
  obtain ⟨t,hs,hc⟩ := hm
  refine ⟨t, ?_, hs, exactInitialEncoder_injective ?_⟩
  · rw [LambdaR, mem_Lambda]
    have hb := Finset.card_le_card hs
    have hv' := hv.1
    dsimp only [initialConstant] at hv' hb
    omega
  · exact hc.trans (exactInitialEncoder_messageCurve t gamma).symm

theorem alpha_match (g : Fin 4 → FinalWord K) (alpha : K)
    (hgood : alpha ∉ B6 g) (r : FinalResponse K) (hv : AlphaValid g alpha r) :
    ∃ t : Fin 4 → FinalMessage K, r.2 ⊆ jointAgreementSet exactFinalEncoder g t ∧
      r.1 = exactFinalMessageCurve t alpha := by
  apply (final_matchingDecomposition_iff g (finalConstant r) alpha).mp
  by_contra hm
  exact hgood ((mem_B6 g alpha).mpr ⟨r,hv,hm⟩)

#print axioms gamma_matched_iff
#print axioms Close_card
#print axioms Lambda_card
#print axioms LambdaR_card
#print axioms LambdaCodewords_card
#print axioms B1_card
#print axioms B6_card
#print axioms gamma_match
#print axioms alpha_match
end
end AspisR0.ListsResponses
