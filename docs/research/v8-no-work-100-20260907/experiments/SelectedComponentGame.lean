import GammaComponentGame
import SelectedQuotientOriginal
import NearGammaSelectedCoefficients
import GammaEligibility

/-! Concrete original-code recovery closes the deterministic coverage input
of the causal gamma/row game. Received C1 and arbitrary late C2, all OOD data,
and individual point claims are fixed before gamma. The tuple is CONSTRUCTED
before gamma and its C1 projection identified with the earlier C1-only object.
Sparse gamma coverage is charged, not discarded. The supported near-final
event is not all acceptance and no executable payment extractor is claimed. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.SelectedComponentGame
open Finset
open AspisV8.GammaComponentGame AspisV8.SelectedReceivedOracle
open AspisV8.OODInterpolant AspisV8.CausalOrderedRelation
open AspisV8.JointImageGame AspisV8.RepresentedImageGame
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.PartialFoldRecovery AspisV8.ClaimTransport
open AspisV8.ShiftedRowPrefix
open AspisV8.NearGammaSelectedCoefficients
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
noncomputable local instance : Fintype (Fin 262144) :=
  AspisV8.EarlyC1Specialization.explicit_instance

def received (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (gamma : K) : Fin 1048576 → K :=
  SelectedQuotientOriginal.virtual (atGamma data gamma)
    (NearGammaSelectedC1.rawBatch c1 c2 gamma)

theorem checked_atGamma (data : Data (K := K)) (checked : data.Checked) (gamma : K) :
    (atGamma data gamma).Checked := checked

/-- Same reconstruction coefficients, not merely pointwise equivalence. -/
theorem original_eq (data : Data (K := K)) (gamma : K) (Q : Fin 1024 → K) :
    ComponentRows.original (atGamma data gamma) Q=(atGamma data gamma).original Q := rfl

theorem close_original (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (checked : data.Checked) (gamma : K) (Q : Fin 1024 → K)
    (close : (fibreBad (m := 262144) (exactInitialEncoder Q)
      (received c1 c2 data gamma)).card≤4*2324)
    (h1 : Q 1023=0) (h2 : (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0) :
    (fibreBad (m := 262144) (exactInitialEncoder (ComponentRows.original (atGamma data gamma) Q))
      (NearGammaSelectedC1.rawBatch c1 c2 gamma)).card≤9301 := by
  rw [original_eq]
  exact (SelectedQuotientOriginal.geometric_2324_to_original
    (atGamma data gamma) (checked_atGamma data checked gamma) Q ⟨h1,h2⟩
    (NearGammaSelectedC1.rawBatch c1 c2 gamma) close).trans (by norm_num)

/-- An image-valid geometric anchor makes gamma good by the actual raw
original-code predicate, including the two deterministic pole fibres. -/
theorem good_of_close_image (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (checked : data.Checked) (Gamma : Finset K) (gamma : K) (hg : gamma∈Gamma)
    (Q : Fin 1024 → K)
    (close : (fibreBad (m := 262144) (exactInitialEncoder Q)
      (received c1 c2 data gamma)).card≤4*2324)
    (h1 : Q 1023=0) (h2 : (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0) :
    gamma∈NearGammaSelectedC1.good c1 c2 Gamma := by
  exact GammaEligibility.good_mem NearGammaSelectedC1.code univ
    (NearGammaSelectedC1.curve c1 c2) 9301 Gamma gamma hg
    (fibreEncode (ComponentRows.original (atGamma data gamma) Q))
    (near_of_fibreBad c1 c2 gamma _ (close_original c1 c2 data checked gamma Q close h1 h2))

theorem unit {q : Nat} (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q) (gamma : K) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q≤domain.card) :
    nearProbability data quarter hq w claimed inactive (received c1 c2 data) 2324
      strategy gamma A G≤1 :=
  GammaComponentAux.rows_unit (rowPrefix data quarter w claimed inactive gamma) hq
    (oracle 0 (received c1 c2 data gamma)) (strategy gamma)
    (AspisV8.PreAnchorJoint.near (received c1 c2 data gamma) 2324 (strategy gamma))
    A G ha hg hcount

/-- Sparse original-code gamma coverage bounds actual compact near-final
acceptance, including invalid images, sparse fold geometry, and scalar-only
query acceptance. No original anchor is assumed to exist. -/
theorem sparse_near_bound {q : Nat}
    (c1 : C1Received) (c2 : C2Received) (data : Data (K := K)) (checked : data.Checked)
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card)
    (sparse : (NearGammaSelectedC1.good c1 c2 Gamma).card<64) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 2324 strategy gamma A G)≤
      63/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  have h := avg_exception Gamma (NearGammaSelectedC1.good c1 c2 Gamma) hgamma
    (GammaEligibility.good_subset NearGammaSelectedC1.code univ
      (NearGammaSelectedC1.curve c1 c2) 9301 Gamma)
    (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 2324 strategy gamma A G)
    (((q:ℚ)+3)/G.card+24/A.card) (by positivity)
    (fun gamma _ => unit c1 c2 data quarter hq w claimed inactive strategy gamma A G ha hg hcount)
    (by
      intro gamma hgam outside
      apply near_bound_of_wrong_rows data quarter hq w claimed inactive (received c1 c2 data)
        2324 strategy gamma A G ha hg hpos hcount (by norm_num)
      intro Q close h1 h2
      exact False.elim (outside (good_of_close_image c1 c2 data checked Gamma gamma hgam Q close h1 h2)))
  have hc : ((NearGammaSelectedC1.good c1 c2 Gamma).card:ℚ)≤63 := by exact_mod_cast (show (NearGammaSelectedC1.good c1 c2 Gamma).card≤63 by omega)
  have bound := h.trans (add_le_add
    (div_le_div_of_nonneg_right hc (Nat.cast_nonneg Gamma.card)) (le_refl _))
  simpa only [add_assoc] using bound

/-- The mathematical C1-only candidate being absent is charged on near
acceptance; it never removes those executions. This is not a claim about
every abort/fuel/cache outcome of an implementation's extraction provider. -/
theorem absent_early_c1_near_bound {q : Nat}
    (c1 : C1Received) (c2 : C2Received) (data : Data (K := K)) (checked : data.Checked)
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card) (absent : earlyC1 c1=none) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 2324 strategy gamma A G)≤
      63/Gamma.card+((q:ℚ)+3)/G.card+24/A.card :=
  sparse_near_bound c1 c2 data checked quarter hq w claimed inactive strategy
    A G Gamma ha hg hgamma hpos hcount
    (NearGammaSelectedC1.no_early_c1_forces_sparse c1 c2 Gamma absent)

/-- The selected source geometry supplies every recovered-close equality.
The tuple is selected before all point claims, OOD data and later strategies
quantified below, so no post-gamma target is frozen retrospectively. -/
theorem component_game_dichotomy (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K) :
    (NearGammaSelectedC1.good c1 c2 Gamma).card<64 ∨
      ∃ p : Fin 29 → Message,
        245609≤(support fibreEncode (fibreWord29 c1 c2) p).card ∧
        earlyC1 c1=some (c1Projection p) ∧
        ∀ (q : Nat) (data : Data (K := K)), data.Checked →
        ∀ (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
          (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
          (strategy : K → K → Strategy domain q)
          (A G : Finset K), A.Nonempty → G.Nonempty → Gamma.Nonempty →
          0<q → q≤domain.card →
          ∀ (j : Fin 3) (lane : Fin 29), claimed j lane≠covector (w j.succ) (p lane) →
          avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
            (received c1 c2 data) 2324 strategy gamma A G)≤
            28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  rcases raw_message_cover_dichotomy c1 c2 Gamma with sparse | ⟨p,own,early,cover⟩
  · exact Or.inl sparse
  · refine Or.inr ⟨p,own,early,?_⟩
    intro q data checked quarter hq w claimed inactive strategy A G ha hg hgamma hpos hcount j lane wrong
    apply wrong_component_near_bound data quarter hq w claimed inactive (received c1 c2 data)
      2324 strategy p j lane wrong A G Gamma ha hg hgamma hpos hcount (by norm_num)
    intro gamma hgam Q close h1 h2
    exact cover gamma hgam _ (close_original c1 c2 data checked gamma Q close h1 h2)

#print axioms checked_atGamma
#print axioms original_eq
#print axioms close_original
#print axioms good_of_close_image
#print axioms unit
#print axioms sparse_near_bound
#print axioms absent_early_c1_near_bound
#print axioms component_game_dichotomy
end
end AspisV8.SelectedComponentGame
