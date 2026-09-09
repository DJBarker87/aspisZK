import ThreeHelperClaimCover

/-! Recover a literal full-domain support for the degree-two helper curve
from an image-valid original-code reconstruction. C1's excluded fibres and
the actual chord poles are charged. No punctured-code theorem or acceptance
implication is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 50000
namespace AspisV8.HelperSupportTransfer
open Finset
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.NearGammaSelectedC1 AspisV8.NearGammaFibreBridge
open AspisV8.FixedC1HelperReduction AspisV8.ThreeHelperSelected
open AspisV8.ThreeHelperClaimCover AspisV8.PartialFoldRecovery
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def retained (received : C1Received) (p : C1Messages) (c2 : C2Received)
    (gamma : K) (message : Message) : Finset (Fin 262144) :=
  ownSupport received p \ rawBad received c2 gamma message univ

/-- The support refers to actual helper evaluations on the full stored
domain. Only its matching subset is restricted, not the code definition. -/
theorem retained_helper_matches (received : C1Received) (p : C1Messages)
    (c2 : C2Received) (gamma : K) (nonzero : gamma≠0) (message : Message) :
    ∀ f∈retained received p c2 gamma message, ∀ slot : Fin 4,
      helperCurve c2 gamma (fibreEmbed (f,slot))=
        exactInitialEncoder (normalized p gamma message) (fibreEmbed (f,slot)) := by
  apply (restricted_support_iff received p c2 gamma nonzero message _ ?_).mp
  · intro f member slot
    have notBad := (mem_sdiff.mp member).2
    have equal : (fun s : Fin 4 => rawBatch received c2 gamma (fibreEmbed (f,s)))=
        fibreEncode message f := by
      by_contra different
      exact notBad (mem_filter.mpr ⟨mem_univ f,different⟩)
    exact congrFun equal slot
  · intro f member slot lane
    exact ownSupport_same received p f (mem_sdiff.mp member).1 slot lane

theorem retained_support_loss (received : C1Received) (p : C1Messages)
    (c2 : C2Received) (gamma : K) (message : Message) :
    (ownSupport received p).card≤(retained received p c2 gamma message).card+
      (fibreBad (m:=262144) (exactInitialEncoder message) (rawBatch received c2 gamma)).card := by
  have loss : (ownSupport received p).card≤
      (retained received p c2 gamma message).card+
        (rawBad received c2 gamma message univ).card := Finset.card_le_card_sdiff_add_card
  exact loss.trans (Nat.add_le_add_left
    (rawBad_card_le_full received c2 gamma message univ) _)

/-- A source-shaped bound before choosing any numerical agreement cutoff. -/
theorem quotient_support_loss (received : C1Received) (p : C1Messages)
    (c2 : C2Received) (gamma : K) (d : OODInterpolant.Data (K:=K))
    (checked : d.Checked) (Q : Message)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0) :
    (ownSupport received p).card≤(retained received p c2 gamma (d.original Q)).card+
      (fibreBad (m:=262144) (exactInitialEncoder Q)
        (SelectedQuotientOriginal.virtual d (rawBatch received c2 gamma))).card+2 := by
  have loss := retained_support_loss received p c2 gamma (d.original Q)
  have poles := SelectedQuotientOriginal.fibreBad_card d checked Q image
    (rawBatch received c2 gamma)
  omega

/-- At least26095 quotient-matching fibres guarantee9558 retained fibres:
26095 - 16535 C1-excluded - 2 possible poles = 9558. This is not an
acceptance-to-distance theorem and does not cover the old9558 cutoff. -/
theorem quotient_26095_retains_9558 (received : C1Received) (p : C1Messages)
    (found : earlyC1 received=some p) (c2 : C2Received) (gamma : K)
    (d : OODInterpolant.Data (K:=K)) (checked : d.Checked) (Q : Message)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (close : (fibreBad (m:=262144) (exactInitialEncoder Q)
      (SelectedQuotientOriginal.virtual d (rawBatch received c2 gamma))).card≤236049) :
    9558≤(retained received p c2 gamma (d.original Q)).card := by
  have own := some_early_has_support fibreEncode (receivedFibres received) 245609 p found
  have loss := quotient_support_loss received p c2 gamma d checked Q image
  change 245609≤(ownSupport received p).card at own
  omega

/-- Actual original-domain evaluations, not a punctured-circle membership
assumption: the normalized message meets the older >38229-symbol floor. -/
theorem normalized_full_domain_support (received : C1Received) (p : C1Messages)
    (found : earlyC1 received=some p) (c2 : C2Received) (gamma : K) (nonzero : gamma≠0)
    (d : OODInterpolant.Data (K:=K)) (checked : d.Checked) (Q : Message)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (close : (fibreBad (m:=262144) (exactInitialEncoder Q)
      (SelectedQuotientOriginal.virtual d (rawBatch received c2 gamma))).card≤236049) :
    38232≤(univ.filter fun index : Fin 1048576 =>
      helperCurve c2 gamma index=exactInitialEncoder (normalized p gamma (d.original Q)) index).card := by
  have enough := quotient_26095_retains_9558 received p found c2 gamma d checked Q image close
  have expanded := fibre_card_bound fibreEmbed (helperCurve c2 gamma)
    (exactInitialEncoder (normalized p gamma (d.original Q)))
    (retained received p c2 gamma (d.original Q))
    (retained_helper_matches received p c2 gamma nonzero (d.original Q))
  rw [Fintype.card_fin] at expanded
  omega

#print axioms retained_helper_matches
#print axioms retained_support_loss
#print axioms quotient_support_loss
#print axioms quotient_26095_retains_9558
#print axioms normalized_full_domain_support
end
end AspisV8.HelperSupportTransfer
