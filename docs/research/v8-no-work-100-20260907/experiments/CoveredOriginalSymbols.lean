import SelectedQuotientOriginal
import QuotientFamilySelected
import SelectedComponentGame
import AspisFormal.V6Width29CorrelatedAgreement

/-! Literal covered quotient -> original-code symbol support. A whole
9558-fibre support contributes 38232 distinct stored symbols; the checked
chord loses at most TWO SYMBOLS, retaining the strict V7 width29 threshold.
No original component tuple, received polynomiality, decoder success, or
off-domain sampler law is a premise. The constructed original candidate may
depend on gamma; it is not moved before its actual selection boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000
namespace AspisV8.CoveredOriginalSymbols
open Finset
open AspisV8.SelectedQuotientOriginal AspisV8.QuotientFamilySelected
open AspisV8.OffFamilyIntersection AspisV8.NearGammaFibreBridge
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV5ComponentCConcreteFoldLinearity
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV6Width29CorrelatedAgreement
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def symbolSupport (left right : Fin 1048576 → K) : Finset (Fin 1048576) :=
  univ.filter fun i => left i=right i

/-- Exact child index is 4*fibre+slot in both retained encoders. -/
theorem embed_is_child (f : Fin 262144) (slot : Fin 4) :
    fibreEmbed (f,slot)=childIndex f slot := rfl

theorem complete_fibres_supply_symbols (received : Fin 1048576 → K)
    (Q : Fin 1024 → K) :
    4*(fullSupport univ received Q).card≤
      (symbolSupport (exactInitialEncoder Q) received).card := by
  have bound := fibre_card_bound fibreEmbed (exactInitialEncoder Q) received
    (fullSupport univ received Q) (by
      intro f member slot
      rw [embed_is_child]
      exact (mem_filter.mp member).2 slot)
  rw [Fintype.card_fin] at bound
  exact bound

/-- Keep precisely the non-pole symbols, not an enlarged loss of all four
symbols in each pole's fibre. Every retained symbol has original agreement. -/
theorem nonpole_support_subset (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K) :
    symbolSupport (exactInitialEncoder Q) (virtual d received) \ poleSymbols d ⊆
      symbolSupport (exactInitialEncoder (d.original Q)) received := by
  intro i member
  obtain ⟨matched,notPole⟩ := mem_sdiff.mp member
  have nonzero : denominator d i≠0 := by
    intro zero
    exact notPole (mem_filter.mpr ⟨mem_univ i,zero⟩)
  exact mem_filter.mpr ⟨mem_univ i,
    (symbol_agreement_iff d checked Q image received i nonzero).mp
      (mem_filter.mp matched).2⟩

theorem original_symbol_loss (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K) :
    (symbolSupport (exactInitialEncoder Q) (virtual d received)).card≤
      (symbolSupport (exactInitialEncoder (d.original Q)) received).card+2 := by
  have loss : (symbolSupport (exactInitialEncoder Q) (virtual d received)).card≤
      (symbolSupport (exactInitialEncoder Q) (virtual d received) \ poleSymbols d).card+
        (poleSymbols d).card := Finset.card_le_card_sdiff_add_card
  have subset := Finset.card_le_card (nonpole_support_subset d checked Q image received)
  have poles := poleSymbols_card d checked
  omega

/-- A member of the literal fixed-word family yields more than38229
original-code symbols. No membership of any component family is inferred. -/
theorem family_member_original_38230 (d : Data (K := K)) (checked : d.Checked)
    (Q : Fin 1024 → K) (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (received : Fin 1048576 → K)
    (member : Q∈literalFamily (virtual d received)) :
    38230≤(symbolSupport (exactInitialEncoder (d.original Q)) received).card := by
  have fibres : 9558≤(fullSupport univ (virtual d received) Q).card :=
    (mem_literalFamily (virtual d received) Q).mp member
  have symbols := complete_fibres_supply_symbols (virtual d received) Q
  have loss := original_symbol_loss d checked Q image received
  omega

/-- The historical width29 curve uses values*gamma^lane, whereas the
selected raw batch uses gamma^lane*values. Only commutativity is needed. -/
theorem raw_batch_eq_curve (c1 : C1Received) (c2 : C2Received)
    (gamma : K) (i : Fin 1048576) :
    NearGammaSelectedC1.rawBatch c1 c2 gamma i=
      width29CurveValue (received29 c1 c2) gamma i := by
  unfold NearGammaSelectedC1.rawBatch width29CurveValue width29Batch
  apply Finset.sum_congr rfl
  intro lane _
  exact mul_comm _ _

def originalStrategy (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (quotient : K → Fin 1024 → K) :
    Width29ProximateStrategy K (Fin 1048576) (Fin 1024 → K) where
  candidate gamma := (atGamma data gamma).original (quotient gamma)
  support gamma := symbolSupport
    (exactInitialEncoder ((atGamma data gamma).original (quotient gamma)))
    (NearGammaSelectedC1.rawBatch c1 c2 gamma)

/-- Exact valid-response interface consumed by the already proved V7
width29 theorem. It is a validity premise DERIVED from a covered image-valid
quotient, not an assumption of component tuple recovery or global coverage. -/
theorem selected_width29_valid (c1 : C1Received) (c2 : C2Received)
    (data : Data (K := K)) (checked : data.Checked)
    (quotient : K → Fin 1024 → K) (gamma : K)
    (image : quotient gamma 1023=0 ∧
      data.b*quotient gamma 1022-data.c*quotient gamma 1021=0)
    (member : quotient gamma∈literalFamily (SelectedComponentGame.received c1 c2 data gamma)) :
    Width29ValidResponse exactInitialEncoder 38229 (received29 c1 c2)
      (originalStrategy c1 c2 data quotient) gamma := by
  constructor
  · have enough := family_member_original_38230 (atGamma data gamma) checked
      (quotient gamma) image (NearGammaSelectedC1.rawBatch c1 c2 gamma) member
    exact Nat.lt_of_lt_of_le (by omega : 38229<38230) enough
  · intro i member
    have matched := (mem_filter.mp member).2
    rw [←raw_batch_eq_curve]
    exact matched.symm

#print axioms embed_is_child
#print axioms complete_fibres_supply_symbols
#print axioms nonpole_support_subset
#print axioms original_symbol_loss
#print axioms family_member_original_38230
#print axioms raw_batch_eq_curve
#print axioms selected_width29_valid
end
end AspisV8.CoveredOriginalSymbols
