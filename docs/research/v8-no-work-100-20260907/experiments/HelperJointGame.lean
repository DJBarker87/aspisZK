import GenericOODClaimGame
import ThreeHelperClaimCover

/-! Joint accepted wrong-claim mass for the enlarged supported-final region.
The actual helper cover supplies every recovered-close equality. The sparse
Good alternative is charged, not discarded. The endpoint constructs one tuple
before OOD data/claims/strategies and has no candidate-membership premise.
Far finals, absent early C1, and payment/source/replay obligations remain. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.HelperJointGame
open Finset
open AspisV8.SelectedReceivedOracle AspisV8.GammaComponentGame
open AspisV8.SelectedComponentGame AspisV8.ComponentOODBinding
open AspisV8.OODInterpolant AspisV8.CausalOrderedRelation
open AspisV8.ShiftedRowPrefix AspisV8.JointImageGame AspisV8.ClaimTransport
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.PartialFoldRecovery AspisV8.NearGammaSelectedCoefficients
open AspisV8.ThreeHelperClaimCover
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance

/-- With fewer than three eligible helper gammas, charge the whole supported
acceptance event. Invalid images and scalar-only query acceptance are retained. -/
theorem sparse_bound {q : Nat}
    (c1 : C1Received) (p : C1Messages) (c2 : C2Received)
    (data : Data (K := K)) (checked : data.Checked)
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (nonzero : ∀ gamma∈Gamma, gamma≠0)
    (hpos : 0<q) (hcount : q≤domain.card)
    (sparse : (goodGammas c1 p c2 Gamma).card<3) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 15334 strategy gamma A G)≤
      2/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  have h := avg_exception Gamma (goodGammas c1 p c2 Gamma) hgamma
    (good_subset c1 p c2 Gamma)
    (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 15334 strategy gamma A G)
    (((q:ℚ)+3)/G.card+24/A.card) (by positivity)
    (fun gamma _ => GenericOODClaimGame.unit c1 c2 data quarter hq w claimed inactive 15334
      strategy gamma A G ha hg hcount)
    (by
      intro gamma hgam outside
      apply near_bound_of_wrong_rows data quarter hq w claimed inactive (received c1 c2 data)
        15334 strategy gamma A G ha hg hpos hcount (by norm_num)
      intro Q close h1 h2
      exact False.elim (outside (ThreeHelperClaimCover.good_of_close_image c1 p c2 Gamma
        gamma hgam (nonzero gamma hgam) (atGamma data gamma)
        (checked_atGamma data checked gamma) Q ⟨h1,h2⟩ close)))
  have hc : ((goodGammas c1 p c2 Gamma).card:ℚ)≤2 := by
    exact_mod_cast (show (goodGammas c1 p c2 Gamma).card≤2 by omega)
  have bound := h.trans (add_le_add
    (div_le_div_of_nonneg_right hc (Nat.cast_nonneg Gamma.card)) (le_refl _))
  simpa only [add_assoc] using bound

def claimMismatch (P : Fin 29 → Message) (data : Data (K := K))
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K) : Prop :=
  (∃ (j : Fin 3) (lane : Fin 29), claimed j lane≠covector (w j.succ) (P lane)) ∨
    ∃ (r : Fin 2) (lane : Fin 29), data.answers r lane≠
      circleFunctional (pointX data r) (pointY data r) (P lane)

/-- The wrong-claim indicator is fixed at the pre-gamma prefix. This is NOT
a probability conditioned on correct claims, a good image, or successful recovery. -/
def badClaimProbability {q : Nat} (P : Fin 29 → Message)
    (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q) (A G Gamma : Finset K) : ℚ := by
  classical
  exact if claimMismatch P data w claimed then
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 15334 strategy gamma A G)
  else 0

/-- Actual early C1 supplies the constructed cover. There exists ONE tuple
with that C1 projection, fixed before every later prefix quantified here.
All supported accepted wrong ordinary/OOD claims are charged, including the
sparse helper branch. This is not a full witness extractor or global bound. -/
theorem early_bad_claim_bound (c1 : C1Received) (p : C1Messages) (c2 : C2Received)
    (Gamma : Finset K) (nonzero : ∀ gamma∈Gamma, gamma≠0)
    (found : earlyC1 c1=some p) :
    ∃ P : Fin 29 → Message, c1Projection P=p ∧
      ∀ (q : Nat) (data : Data (K := K)), data.Checked →
      data.x0^2+data.y0^2=1 ∧ data.x1^2+data.y1^2=1 →
      ∀ (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
        (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
        (strategy : K → K → Strategy domain q)
        (A G : Finset K), A.Nonempty → G.Nonempty → Gamma.Nonempty →
        0<q → q≤domain.card →
        badClaimProbability P c1 c2 data quarter hq w claimed inactive strategy A G Gamma≤
          28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  classical
  rcases quotient_cover_dichotomy c1 p c2 Gamma nonzero found with sparse | ⟨P,projection,cover⟩
  · refine ⟨join p (fun _ => 0),join_projection p (fun _ => 0),?_⟩
    intro q data checked circles quarter hq w claimed inactive strategy A G ha hg hgamma hpos hcount
    unfold badClaimProbability
    split_ifs
    · have bound := sparse_bound c1 p c2 data checked quarter hq w claimed inactive strategy
        A G Gamma ha hg hgamma nonzero hpos hcount sparse
      have cap : (2:ℚ)/Gamma.card≤28/Gamma.card :=
        div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg Gamma.card)
      exact bound.trans (add_le_add (add_le_add cap (le_refl _)) (le_refl _))
    · positivity
  · refine ⟨P,projection,?_⟩
    intro q data checked circles quarter hq w claimed inactive strategy A G ha hg hgamma hpos hcount
    unfold badClaimProbability
    split_ifs with wrong
    · rcases wrong with ⟨j,lane,hwrong⟩ | ⟨r,lane,hwrong⟩
      · apply wrong_component_near_bound data quarter hq w claimed inactive (received c1 c2 data)
          15334 strategy P j lane hwrong A G Gamma ha hg hgamma hpos hcount (by norm_num)
        intro gamma hgam Q close h1 h2
        exact cover (atGamma data gamma) (checked_atGamma data checked gamma)
          gamma hgam Q ⟨h1,h2⟩ close
      · apply GenericOODClaimGame.wrong_ood_bound c1 c2 Gamma P 15334 data checked circles
          quarter hq w claimed inactive strategy A G ha hg hgamma hpos hcount (by norm_num)
          ?_ r lane hwrong
        intro gamma hgam Q close h1 h2
        exact cover (atGamma data gamma) (checked_atGamma data checked gamma)
          gamma hgam Q ⟨h1,h2⟩ close
    · positivity

/-- The C1-facing endpoint no longer mentions a chosen helper tuple. Its
target is literally the earlier C1-only object. This still binds claims at
the pre-gamma boundary; it does not move semantic challenges backwards. -/
theorem early_c1_wrong_claim_bound {q : Nat}
    (c1 : C1Received) (p : C1Messages) (c2 : C2Received)
    (Gamma : Finset K) (nonzero : ∀ gamma∈Gamma, gamma≠0)
    (found : earlyC1 c1=some p)
    (data : Data (K := K)) (checked : data.Checked)
    (circles : data.x0^2+data.y0^2=1 ∧ data.x1^2+data.y1^2=1)
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card)
    (wrong : (∃ (j : Fin 3) (lane : Fin 26),
        claimed j (AspisPool.V7ExtractedLaneWords.c1LaneIndex lane)≠
          covector (w j.succ) (p lane)) ∨
      ∃ (r : Fin 2) (lane : Fin 26),
        data.answers r (AspisPool.V7ExtractedLaneWords.c1LaneIndex lane)≠
          circleFunctional (pointX data r) (pointY data r) (p lane)) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 15334 strategy gamma A G)≤
      28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  classical
  obtain ⟨P,projection,bound⟩ := early_bad_claim_bound c1 p c2 Gamma nonzero found
  have mismatch : claimMismatch P data w claimed := by
    rcases wrong with ⟨j,lane,hwrong⟩ | ⟨r,lane,hwrong⟩
    · left
      refine ⟨j,AspisPool.V7ExtractedLaneWords.c1LaneIndex lane,?_⟩
      have same := congrFun projection lane
      change P (AspisPool.V7ExtractedLaneWords.c1LaneIndex lane)=p lane at same
      rw [same]
      exact hwrong
    · right
      refine ⟨r,AspisPool.V7ExtractedLaneWords.c1LaneIndex lane,?_⟩
      have same := congrFun projection lane
      change P (AspisPool.V7ExtractedLaneWords.c1LaneIndex lane)=p lane at same
      rw [same]
      exact hwrong
  have result := bound q data checked circles quarter hq w claimed inactive strategy
    A G ha hg hgamma hpos hcount
  simpa only [badClaimProbability,if_pos mismatch] using result

#print axioms sparse_bound
#print axioms early_bad_claim_bound
#print axioms early_c1_wrong_claim_bound
end
end AspisV8.HelperJointGame
