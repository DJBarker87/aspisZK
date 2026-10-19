import R1SecondFoldMatched
import R1ParentSupport
import SecondFoldSparseProjectionCore

/-! Concrete fourfold agreement transfer to the sparse 64-message image. -/

set_option autoImplicit false

namespace AspisR1.SecondFoldSparseProjectionBridge

open AspisR1.ConcreteProjection
open AspisR1.SecondFoldMatched
open AspisR1.SecondFoldSparseProjectionCore
open AspisWide.Agreement
open AspisWide.FinalEncoder

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- A 2390-parent match becomes 9560 matching children for the repeated
received word, clearing the final decoder's 9558 agreement threshold. -/
theorem sparseLift_final_agreement_of_second_match
    (received : SmallWord K) (m : SmallMessage K)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hmatch : ∀ i ∈ S, secondEncoder m i = received i) :
    9558 ≤ (agreementSet
      (exactFinalEncoder (AspisR1.sparseLift m))
      (repeatedWord received)).card := by
  have hsubset : AspisR1.fullQuartetSet S ⊆ agreementSet
      (exactFinalEncoder (AspisR1.sparseLift m)) (repeatedWord received) := by
    intro k hk
    simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hi := AspisR1.parentIndex_mem_of_mem_fullQuartetSet S hk
    rw [← AspisR1.childIndex_parentIndex_slotIndex (n := 65536) k]
    rw [AspisR1.ConcreteProjection.exactFinal_sparseLift_child]
    simpa only [repeatedWord, AspisR1.parentIndex_childIndex] using
      hmatch (AspisR1.parentIndex k) hi
  have hcard := Finset.card_le_card hsubset
  have hrepeat := AspisR1.repeated_support_card_ge_9560 S hS
  have hcardEq : (AspisR1.repeatedSupport S).card =
      (AspisR1.fullQuartetSet S).card := by
    rw [AspisR1.repeated_support_card, AspisR1.fullQuartetSet_card]
  have hquartets : 9560 ≤ (AspisR1.fullQuartetSet S).card :=
    hrepeat.trans_eq hcardEq
  omega

/-- Completeness transfer from the final decoder's finite candidate list to
the sparse projection. The decoder premise is its standard threshold
completeness for this repeated received word. -/
theorem second_match_survives_projection
    (received : SmallWord K) (m : SmallMessage K)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hmatch : ∀ i ∈ S, secondEncoder m i = received i)
    (finalCandidates : List (Fin 256 → K))
    (hdecode : ∀ a : Fin 256 → K,
      9558 ≤ (agreementSet (exactFinalEncoder a) (repeatedWord received)).card →
        a ∈ finalCandidates) :
    m ∈ projectFinalCandidates finalCandidates := by
  apply projectFinalCandidates_mem_iff.mpr
  refine ⟨AspisR1.sparseLift m, hdecode (AspisR1.sparseLift m)
    (sparseLift_final_agreement_of_second_match received m S hS hmatch), rfl⟩

#print axioms projectSparseCandidate
#print axioms projectFinalCandidates
#print axioms sparseLift_final_agreement_of_second_match
#print axioms second_match_survives_projection

end AspisR1.SecondFoldSparseProjectionBridge
