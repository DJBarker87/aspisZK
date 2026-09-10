import SelectedRegularLowSupport
import SelectedComponentGame

/-! Source-review draft: outside the existing fixed original-code Good set,
every image-valid quotient of the actual virtual received word has at most
252847 full fibres. If the C1-only optional object is absent, that Good set
has at most 63 elements. The same Q supplies image validity and support;
Q is quantified after gamma and may be selected at any later history.

This is a deterministic support partition, not a probability, acceptance,
regularity, or payment-extraction theorem. In particular, the middle band
200808..252847 is not removed by the absence of an early C1 candidate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000

namespace AspisV8.SelectedHigherYNoEarlySupport
open Finset
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV8.CausalCoveredRecovery AspisV8.SelectedRegularLowSupport
open AspisV8.OODInterpolant AspisV8.PartialFoldRecovery
open AspisV8.GammaComponentGame
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- The actual quotient-fibre budget enters the already checked raw
original-code Good predicate, including the source's deterministic pole
loss. No early-C1 existence or gamma-nonzero premise is needed here. -/
theorem large_support_mem_good {q : Nat} (e : Execution q)
    (checked : e.data.Checked) (Gamma : Finset K) (gamma : K)
    (member : gamma ∈ Gamma) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧
      (atGamma e.data gamma).b*Q 1022-(atGamma e.data gamma).c*Q 1021=0)
    (large : 252848 ≤ fibreCount (e.raw gamma) Q) :
    gamma ∈ NearGammaSelectedC1.good e.c1 e.c2 Gamma := by
  have total := full_bad_card (e.raw gamma) Q
  have close : (fibreBad (m := 262144) (exactInitialEncoder Q)
      (e.raw gamma)).card ≤ 4*2324 := by omega
  exact SelectedComponentGame.good_of_close_image e.c1 e.c2 e.data checked
    Gamma gamma member Q close image.1 image.2

/-- A bound for EVERY actual image-valid Q outside Good, not a bound for
one chosen decoder result. Absence of early C1 is not necessary for this
pointwise implication; it is used only to bound Good in the endpoint below. -/
theorem outside_good_support_cap {q : Nat} (e : Execution q)
    (checked : e.data.Checked) (Gamma : Finset K) (gamma : K)
    (member : gamma ∈ Gamma) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧
      (atGamma e.data gamma).b*Q 1022-(atGamma e.data gamma).c*Q 1021=0)
    (outside : gamma ∉ NearGammaSelectedC1.good e.c1 e.c2 Gamma) :
    fibreCount (e.raw gamma) Q ≤ 252847 := by
  by_contra large
  exact outside (large_support_mem_good e checked Gamma gamma member Q image (by omega))

/-- The exception set is the literal fixed Good(c1,c2,Gamma), not a set
chosen after observing a quotient or a final. Its cardinality and uniform
complement support cap are both derived. The original Gamma is unchanged. -/
theorem no_early_support_cover {q : Nat} (e : Execution q)
    (checked : e.data.Checked) (Gamma : Finset K)
    (absent : EarlyC1Projection.earlyC1 e.c1=none) :
    (NearGammaSelectedC1.good e.c1 e.c2 Gamma).card ≤ 63 ∧
      ∀ gamma ∈ Gamma, ∀ Q : Fin 1024 → K,
        (Q 1023=0 ∧
          (atGamma e.data gamma).b*Q 1022-(atGamma e.data gamma).c*Q 1021=0) →
        gamma ∉ NearGammaSelectedC1.good e.c1 e.c2 Gamma →
        fibreCount (e.raw gamma) Q ≤ 252847 := by
  have sparse := NearGammaSelectedC1.no_early_c1_forces_sparse e.c1 e.c2 Gamma absent
  refine ⟨by omega, ?_⟩
  intro gamma member Q image outside
  exact outside_good_support_cap e checked Gamma gamma member Q image outside

#print axioms large_support_mem_good
#print axioms outside_good_support_cap
#print axioms no_early_support_cover
end
end AspisV8.SelectedHigherYNoEarlySupport
