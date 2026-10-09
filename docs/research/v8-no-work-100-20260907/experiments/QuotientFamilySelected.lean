import QuotientFamilyCore
import SelectedMaskedCurveTail

/-! Literal selected quotient family, fixed by the arbitrary received word.
The finite set contains exactly every Q with at least9558 whole-fibre matches.
No image predicate, decoder/provider filter, or efficient enumeration is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.QuotientFamilySelected
open Finset
open AspisV8.QuotientFamilyCore AspisV8.SelectedMaskedCurveTail
open AspisV8.MaskedCurveRepresentation AspisV8.OffFamilyIntersection
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV5ComponentCConcreteFoldLinearity AspisV5ComponentCQM31TowerExact
open AspisV5FriCoherentCandidateExtraction
noncomputable section

theorem literal_support_intersection_le_255
    (received : Fin 1048576 → QM31Exact) (Q Q' : Fin 1024 → QM31Exact)
    (different : Q≠Q') :
    ((OffFamilyIntersection.fullSupport Finset.univ received Q)∩
      (OffFamilyIntersection.fullSupport Finset.univ received Q')).card≤255 := by
  have inverse := canonical_one_fold_schedule_exact 0
  rw [←actual_support received Q,←actual_support received Q']
  exact fullSupport_intersection_le exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x (canonicalOneFoldSchedule 0).circleInv2y
    inverse.1 inverse.2 exactFinalEncoder_overlap_cap received Q Q' different

theorem literal_finite_subfamily_card_le_99 (received : Fin 1048576 → QM31Exact)
    (candidates : Finset (Fin 1024 → QM31Exact))
    (large : ∀ Q∈candidates, Q∈CandidateFamily Finset.univ received 9558) :
    candidates.card≤99 := by
  have inverse := canonical_one_fold_schedule_exact 0
  apply finite_subfamily_card_le_99 exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x (canonicalOneFoldSchedule 0).circleInv2y
    inverse.1 inverse.2 (by rfl) exactFinalEncoder_overlap_cap received candidates
  intro Q member
  rw [actual_support received Q]
  exact large Q member

theorem exists_literal_family (received : Fin 1048576 → QM31Exact) :
    ∃ family : Finset (Fin 1024 → QM31Exact), family.card≤99 ∧
      ∀ Q, Q∈family ↔ Q∈CandidateFamily Finset.univ received 9558 :=
  exact_finite_family (fun Q => Q∈CandidateFamily Finset.univ received 9558) 99
    (literal_finite_subfamily_card_le_99 received)

/-- Mathematical finite family, not an executable resource-bounded decoder.
Its only variable input is the fixed received quotient word. -/
def literalFamily (received : Fin 1048576 → QM31Exact) : Finset (Fin 1024 → QM31Exact) :=
  Classical.choose (exists_literal_family received)

theorem literalFamily_card_le_99 (received : Fin 1048576 → QM31Exact) :
    (literalFamily received).card≤99 :=
  (Classical.choose_spec (exists_literal_family received)).1

theorem mem_literalFamily (received : Fin 1048576 → QM31Exact) (Q : Fin 1024 → QM31Exact) :
    Q∈literalFamily received ↔ Q∈CandidateFamily Finset.univ received 9558 :=
  (Classical.choose_spec (exists_literal_family received)).2 Q

theorem literalFamily_exact (received : Fin 1048576 → QM31Exact) :
    (↑(literalFamily received) : Set (Fin 1024 → QM31Exact))=
      CandidateFamily Finset.univ received 9558 := by
  ext Q
  exact mem_literalFamily received Q

theorem candidateFamily_ncard_le_99 (received : Fin 1048576 → QM31Exact) :
    (CandidateFamily Finset.univ received 9558).ncard≤99 := by
  rw [←literalFamily_exact received,Set.ncard_coe_finset]
  exact literalFamily_card_le_99 received

#print axioms literal_support_intersection_le_255
#print axioms literal_finite_subfamily_card_le_99
#print axioms exists_literal_family
#print axioms mem_literalFamily
#print axioms candidateFamily_ncard_le_99
end
end AspisV8.QuotientFamilySelected
