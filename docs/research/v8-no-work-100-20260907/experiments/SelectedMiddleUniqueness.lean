import SelectedRegularLowSupport
import NearGammaFibreBridge

/-! Same-gamma middle-support uniqueness for the actual selected encoder.
The two witnesses may come from different factors and different later
kappa/tau/alpha histories. No regularity or fixed early-C1 candidate is
needed. The canonical quotient below is a classical analysis object, not
an online prover choice or an executable extractor. No probability bound
or improvement to the existing gamma-incidence budget is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedMiddleUniqueness
open Finset
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.CausalCoveredRecovery AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedRegularLowSupport AspisV8.OffFamilyIntersection
open AspisV8.NearGammaFibreBridge
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Distinct natural1024 quotients cannot both match too many complete
fibres of the same arbitrary received word. No received polynomiality. -/
theorem support_sum_le (received : Fin 1048576 → K)
    (left right : Fin 1024 → K) (different : left ≠ right) :
    fibreCount received left + fibreCount received right ≤ 262144+256 := by
  let S := fullSupport univ received left
  let T := fullSupport univ received right
  have subset : S ∩ T ⊆ fullFibreAgreement left right := by
    intro i member
    obtain ⟨inS, inT⟩ := Finset.mem_inter.mp member
    have leftSlots := (Finset.mem_filter.mp inS).2
    have rightSlots := (Finset.mem_filter.mp inT).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro slot
    have indexEq : fibreEmbed (i, slot)=childIndex i slot := by
      apply Fin.ext
      rfl
    rw [indexEq]
    exact (leftSlots slot).trans (rightSlots slot).symm
  have overlap : (S ∩ T).card ≤ 256 :=
    (Finset.card_le_card subset).trans (full_fibre_overlap_le_256 left right different)
  have union : (S ∪ T).card ≤ 262144 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (S ∪ T)
  have identity := Finset.card_union_add_card_inter S T
  change S.card+T.card ≤ 262144+256
  omega

/-- Inclusion-exclusion quantifies the common support before using code
distance. The lower bound is 139472 actual complete fibres. -/
theorem support_intersection_large (received : Fin 1048576 → K)
    (left right : Fin 1024 → K)
    (leftLarge : 200808 ≤ fibreCount received left)
    (rightLarge : 200808 ≤ fibreCount received right) :
    139472 ≤ (fullSupport univ received left ∩ fullSupport univ received right).card := by
  let S := fullSupport univ received left
  let T := fullSupport univ received right
  have union : (S ∪ T).card ≤ 262144 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (S ∪ T)
  have identity := Finset.card_union_add_card_inter S T
  change 200808 ≤ S.card at leftLarge
  change 200808 ≤ T.card at rightLarge
  change 139472 ≤ (S ∩ T).card
  omega

/-- The geometric result is stronger than image-valid witness uniqueness:
it applies to all natural1024 quotients with these actual support bounds. -/
theorem high_support_unique (received : Fin 1048576 → K)
    (left right : Fin 1024 → K)
    (leftLarge : 200808 ≤ fibreCount received left)
    (rightLarge : 200808 ≤ fibreCount received right) : left=right := by
  by_contra different
  have bound := support_sum_le received left right different
  omega

/-- Source-shaped endpoint. Witness includes the literal family, image
and row gates, actual adaptive final, and its own retained higher factor.
Those factors and all three later challenges need not agree. -/
theorem high_witness_unique {q : Nat} (e : Execution q) (gamma : K)
    (kappa0 tau0 alpha0 kappa1 tau1 alpha1 : K) (left right : Fin 1024 → K)
    (_leftWitness : Witness e gamma kappa0 tau0 alpha0 left)
    (_rightWitness : Witness e gamma kappa1 tau1 alpha1 right)
    (leftLarge : 200808 ≤ fibreCount (e.raw gamma) left)
    (rightLarge : 200808 ≤ fibreCount (e.raw gamma) right) : left=right :=
  high_support_unique (e.raw gamma) left right leftLarge rightLarge

def MiddleWitness {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (Q : Fin 1024 → K) : Prop :=
  Witness e gamma kappa tau alpha Q ∧
    200808 ≤ fibreCount (e.raw gamma) Q ∧ fibreCount (e.raw gamma) Q ≤ 252847

def HasMiddle {q : Nat} (e : Execution q) (gamma : K) : Prop :=
  ∃ Q, ∃ kappa tau alpha, MiddleWitness e gamma kappa tau alpha Q

/-- Total analysis representative. Its definition quantifies over all
later histories of the fixed execution; it is not a transcript operation.
The zero value in the inactive case has no witness assertion. -/
def canonical {q : Nat} (e : Execution q) (gamma : K) : Fin 1024 → K :=
  if active : HasMiddle e gamma then Classical.choose active else 0

theorem canonical_spec {q : Nat} (e : Execution q) (gamma : K)
    (active : HasMiddle e gamma) :
    ∃ kappa tau alpha, MiddleWitness e gamma kappa tau alpha (canonical e gamma) := by
  have chosen := Classical.choose_spec active
  simpa only [canonical, dif_pos active] using chosen

/-- Once some middle history exists, the canonical quotient agrees with
every high-support witness, even if its factor/history is different. -/
theorem canonical_eq {q : Nat} (e : Execution q) (gamma : K)
    (active : HasMiddle e gamma) (kappa tau alpha : K) (Q : Fin 1024 → K)
    (witness : Witness e gamma kappa tau alpha Q)
    (large : 200808 ≤ fibreCount (e.raw gamma) Q) : canonical e gamma=Q := by
  obtain ⟨kappa0, tau0, alpha0, chosen⟩ := canonical_spec e gamma active
  exact high_witness_unique e gamma kappa0 tau0 alpha0 kappa tau alpha
    (canonical e gamma) Q chosen.1 witness chosen.2.1 large

/-- The actual final remains alpha-adaptive: it equals the alpha fold of
the common analysis quotient, not one final frozen before alpha. -/
theorem canonical_final {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (Q : Fin 1024 → K) (witness : MiddleWitness e gamma kappa tau alpha Q) :
    (e.strategy gamma kappa).final tau alpha=
      coefficientFoldLayer 256 alpha (canonical e gamma) := by
  have active : HasMiddle e gamma := ⟨Q, kappa, tau, alpha, witness⟩
  have same := canonical_eq e gamma active kappa tau alpha Q witness.1 witness.2.1
  rw [same]
  exact witness.1.2.2.1

theorem canonical_inactive {q : Nat} (e : Execution q) (gamma : K)
    (inactive : ¬HasMiddle e gamma) : canonical e gamma=0 := by
  simp only [canonical, dif_neg inactive]

#print axioms support_sum_le
#print axioms support_intersection_large
#print axioms high_support_unique
#print axioms high_witness_unique
#print axioms canonical_spec
#print axioms canonical_eq
#print axioms canonical_final
#print axioms canonical_inactive
end
end AspisV8.SelectedMiddleUniqueness
