import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchController
import AspisFormal.K1.V7Tag73K13IdealErrorLedger

/-!
# Accounting for candidate-directed query-batch routing

There are exactly `64 * 8 = 512` possible q16 terminal slots.  Covering the
accepted terminal slot by a finite union therefore multiplies only the
degree-sixteen nonzero-QM31 collision term by 512.  This deliberately avoids
claiming that a post-q16 role can always be identified before an adaptively
early SHA answer is exposed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting

open MeasureTheory
open scoped ENNReal
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

theorem q16_candidate_terminal_slot_card :
    Fintype.card Q16DigestSlot = 512 := by
  simp [Q16DigestSlot]

/-- Conservative union-bound replacement for the single selected-role joint
batch term. -/
def candidateDirectedJointBatchRawError : ENNReal :=
  (8192 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)

theorem candidate_directed_joint_batch_numerator :
    (8192 : Nat) = 512 * 16 := by norm_num

/-- A finite union over all pre-fixed q16 terminal-slot hypotheses costs
exactly the advertised factor of 512.  This theorem contains only measure
accounting: the protocol-specific actual-law theorem must still prove the
degree-sixteen bound separately for each candidate event. -/
theorem candidate_directed_joint_batch_union_probability_le
    {Sample : Type}
    (law : OuterMeasure Sample)
    (event : Q16DigestSlot → Set Sample)
    (perCandidate : ∀ target,
      law (event target) ≤
        (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) :
    law (⋃ target, event target) ≤ candidateDirectedJointBatchRawError := by
  calc
    law (⋃ target, event target) ≤
        ∑ target : Q16DigestSlot, law (event target) :=
      measure_iUnion_fintype_le law event
    _ ≤ ∑ _target : Q16DigestSlot,
        (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun target _member ↦ perCandidate target
    _ = (Fintype.card Q16DigestSlot : ENNReal) *
        ((16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) := by
      simp
    _ = candidateDirectedJointBatchRawError := by
      rw [q16_candidate_terminal_slot_card]
      unfold candidateDirectedJointBatchRawError
      simp only [div_eq_mul_inv]
      ring

/-- Even the conservative 512-hypothesis union remains below `2^-110`; it is
far below the q16 term that controls the existing `2^-73` K1.3 envelope. -/
theorem candidate_directed_joint_batch_raw_error_le_two_pow_neg110 :
    candidateDirectedJointBatchRawError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 110) := by
  unfold candidateDirectedJointBatchRawError
  have leftFinite :
      ((8192 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  apply (ENNReal.toReal_le_toReal leftFinite (by norm_num)).mp
  norm_num [P]

/-- The complete K1.3 ledger with the 512-way candidate cover. -/
def candidateDirectedK13RawError : ENNReal :=
  exactQ16IdealRawError + exactOneFoldIdealRawError +
    candidateDirectedJointBatchRawError + exactLaterRelationAlphaIdealRawError

/-- Paying the full 512-way cover does not change the established coarse
`2^-73` K1.3 security envelope. -/
theorem candidate_directed_k13_raw_error_le_two_pow_neg73 :
    candidateDirectedK13RawError ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 73) := by
  unfold candidateDirectedK13RawError exactQ16IdealRawError
    exactOneFoldIdealRawError candidateDirectedJointBatchRawError
    exactLaterRelationAlphaIdealRawError
  rw [Nat.choose_eq_descFactorial_div_factorial]
  have q16Finite :
      (((Nat.descFactorial 9557 16 / Nat.factorial 16 : Nat) : ENNReal) /
        (exactK13CompactFavourable : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp)
      (by norm_num [exactK13CompactFavourable])
  have oneFoldFinite :
      ((foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  have firstFinite :
      (((Nat.descFactorial 9557 16 / Nat.factorial 16 : Nat) : ENNReal) /
          (exactK13CompactFavourable : ENNReal) +
        (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨q16Finite, oneFoldFinite⟩
  have jointBatchFinite :
      ((8192 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  have firstThreeFinite :
      ((((Nat.descFactorial 9557 16 / Nat.factorial 16 : Nat) : ENNReal) /
            (exactK13CompactFavourable : ENNReal) +
          (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) +
        (8192 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨firstFinite, jointBatchFinite⟩
  have laterAlphaFinite :
      ((18 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)) ≠ ∞ :=
    ENNReal.div_ne_top (by simp) (by norm_num [P])
  apply (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.2 ⟨firstThreeFinite, laterAlphaFinite⟩)
    (by norm_num)).mp
  rw [ENNReal.toReal_add firstThreeFinite laterAlphaFinite,
    ENNReal.toReal_add firstFinite jointBatchFinite,
    ENNReal.toReal_add q16Finite oneFoldFinite]
  norm_num [exactK13CompactFavourable, foldChallengeCap, P,
    Nat.descFactorial, Nat.factorial]

#print axioms q16_candidate_terminal_slot_card
#print axioms candidateDirectedJointBatchRawError
#print axioms candidate_directed_joint_batch_numerator
#print axioms candidate_directed_joint_batch_union_probability_le
#print axioms candidate_directed_joint_batch_raw_error_le_two_pow_neg110
#print axioms candidateDirectedK13RawError
#print axioms candidate_directed_k13_raw_error_le_two_pow_neg73

end
end AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
