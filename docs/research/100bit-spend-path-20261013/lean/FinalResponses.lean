import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Wide.DegreeThreeMatched
import Wide.Terminal

/-! Field-generic final-response counting factored away from the wider
initial-encoder, masking, and list-decoding dependency tree. This preserves the
existing degree-three threshold and challenge cap. -/

set_option autoImplicit false

namespace AspisR1.FinalResponses

open AspisCircleGroupOrder (P)
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.Agreement
open AspisWide.DegreeThreeMatched
open AspisWide.FinalEncoder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6PublishedTheoremInterfaces

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

abbrev FinalResponse (K : Type) := FinalMessage K × Finset (Fin 262144)

def finalConstant (r : FinalResponse K) :
    ProximateStrategy K (Fin 262144) (FinalMessage K) :=
  ⟨fun _ => r.1, fun _ => r.2⟩

def AlphaValid (g : Fin 4 → FinalWord K) (alpha : K)
    (r : FinalResponse K) : Prop :=
  ValidResponse exactFinalEncoder 9557 g (finalConstant r) alpha

def AlphaMatched (g : Fin 4 → FinalWord K) (alpha : K)
    (r : FinalResponse K) : Prop :=
  HasMatchingDecomposition exactFinalEncoder g (finalConstant r) alpha

def AlphaBad (g : Fin 4 → FinalWord K) (alpha : K)
    (r : FinalResponse K) : Prop :=
  AlphaValid g alpha r ∧ ¬ AlphaMatched g alpha r

def B6 (g : Fin 4 → FinalWord K) : Finset K := by
  classical
  exact Finset.univ.filter fun alpha => ∃ r, AlphaBad g alpha r

@[simp] theorem mem_B6 (g : Fin 4 → FinalWord K) (alpha : K) :
    alpha ∈ B6 g ↔ ∃ r, AlphaBad g alpha r := by
  simp [B6]

/-! Inline form of the existing response-selection helper. It selects an
offending response when one exists and otherwise returns the inhabited default. -/
def selected {C R : Type*} [Inhabited R] (bad : C → R → Prop) (x : C) : R := by
  classical
  exact if h : ∃ r, bad x r then Classical.choose h else default

theorem selected_spec {C R : Type*} [Inhabited R]
    (bad : C → R → Prop) (x : C) (h : ∃ r, bad x r) :
    bad x (selected bad x) := by
  classical
  simpa only [selected, dif_pos h] using Classical.choose_spec h

/-- Exact matched-response decomposition for the released final encoder. -/
theorem final_matchingDecomposition_iff
    (lanes : Fin 4 → FinalWord K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalMessage K)) (z : K) :
    HasMatchingDecomposition exactFinalEncoder lanes strategy z ↔
      ∃ components : Fin 4 → FinalMessage K,
        strategy.support z ⊆ jointAgreementSet exactFinalEncoder lanes components ∧
        strategy.candidate z = exactFinalMessageCurve components z := by
  constructor
  · rintro ⟨components, support, onCurve⟩
    refine ⟨components, support, exactFinalEncoder_injective ?_⟩
    exact onCurve.trans (exactFinalEncoder_messageCurve components z).symm
  · rintro ⟨components, support, candidate⟩
    refine ⟨components, support, ?_⟩
    change exactFinalEncoder (strategy.candidate z) = _
    rw [candidate]
    exact exactFinalEncoder_messageCurve components z

theorem exactFinal_bad_response_challenges_card_le
    (lanes : Fin 4 → FinalWord K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalMessage K)) :
    (goodChallenges exactFinalEncoder 9557 lanes
    (badStrategy exactFinalEncoder 9557 lanes strategy)).card ≤ foldChallengeCap := by
  let hcurve : DegreeThreeCurveDecodable
      (AspisWide.FinalEncoder.exactFinalEncoder (K := K)) 9557 foldChallengeCap :=
    AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable (E := K)
  exact degreeThree_bad_response_challenges_card_le exactFinalEncoder 9557
    foldChallengeCap hcurve lanes strategy

theorem B6_card (g : Fin 4 → FinalWord K) :
    (B6 g).card ≤ 9396508281246 := by
  classical
  letI : Inhabited (FinalResponse K) := ⟨(0, ∅)⟩
  let response := selected (AlphaBad g)
  let strategy : ProximateStrategy K (Fin 262144) (FinalMessage K) :=
    ⟨fun z => (response z).1, fun z => (response z).2⟩
  have subset : B6 g ⊆ goodChallenges exactFinalEncoder 9557 g
      (badStrategy exactFinalEncoder 9557 g strategy) := by
    intro z hz
    apply (mem_badStrategy_good_iff _ _ _ _ _).mpr
    exact selected_spec (AlphaBad g) z ((mem_B6 g z).mp hz)
  exact (Finset.card_le_card subset).trans
    (exactFinal_bad_response_challenges_card_le g strategy)

theorem alpha_match (g : Fin 4 → FinalWord K) (alpha : K)
    (hgood : alpha ∉ B6 g) (r : FinalResponse K)
    (hv : AlphaValid g alpha r) :
    ∃ t : Fin 4 → FinalMessage K,
      r.2 ⊆ jointAgreementSet exactFinalEncoder g t ∧
      r.1 = exactFinalMessageCurve t alpha := by
  apply (final_matchingDecomposition_iff g (finalConstant r) alpha).mp
  by_contra hm
  exact hgood ((mem_B6 g alpha).mpr ⟨r, hv, hm⟩)

#print axioms final_matchingDecomposition_iff
#print axioms exactFinal_bad_response_challenges_card_le
#print axioms B6_card
#print axioms alpha_match

end
end AspisR1.FinalResponses
