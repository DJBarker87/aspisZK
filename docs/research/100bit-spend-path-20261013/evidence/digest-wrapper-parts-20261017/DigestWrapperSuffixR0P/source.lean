import DigestWrapperSuffix
import DigestFixedPrefixR0P

set_option autoImplicit false
namespace AspisR1.DigestWrapperSuffix.R0PBridge
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
open AspisR1.DigestFixedBinding
open AspisR1.DigestFixedPrefix
open AspisR1.DigestFixedPrefix.R0PBridge

attribute [local irreducible] R0P.digestAddBinding
  AspisR1.SelectorValueLaneModelComposition.pointSelector

/-- The checked candidate suffix is the exact tail of the retained digest
relation; the conditional next-frontier access uses that same public carry. -/
theorem model_eq_r0p (point : Array QM 10#usize) (openings : Openings)
    (public1 : Public) (initial : R0P.Digest ExactQM) :
    AspisR1.DigestWrapperSuffix.model point openings.z public1 initial =
      DigestModelDecomposition.suffixFold (SemanticPublicModel.exactPublic public1)
        (exactOpenings openings) (pointSelector point) initial := by
  unfold AspisR1.DigestWrapperSuffix.model DigestModelDecomposition.suffixFold
    DigestModelDecomposition.suffixKeys DigestModelDecomposition.foldStep
  by_cases hc : R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val < 20
  · simp only [SemanticPublicModel.exactPublic, hc, if_pos, _root_.dite_true, List.foldl_append,
      List.foldl_cons, List.foldl_nil, step, R0P.digestRow, R0P.digestStart,
      R0P.digestTarget, R0P.g2Row]
    rw [← opened_model]
    simp only [Nat.mul_comm]
    all_goals rfl
  · simp only [SemanticPublicModel.exactPublic, hc, if_neg, _root_.dite_false, List.foldl_append,
      List.foldl_cons, List.foldl_nil, step, R0P.digestRow, R0P.digestStart,
      R0P.digestTarget, R0P.g2Row]
    rw [← opened_model]
    simp only [Nat.mul_comm]
    all_goals rfl

/-- All source suffix successes are derived; only the actual public/opening
bounds and already-returned boxed selector are inputs. -/
theorem source_success_r0p (point : Array QM 10#usize) (selectors : Selectors)
    (initial : Array QM 8#usize) (openings : Openings) (public1 : Public)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hinitial : CanonicalArray initial) (hopened : CanonicalArray openings.z)
    (hroot : DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt))) :
    ∃ out, run initial openings.z selectors public1 = .ok out ∧ CanonicalArray out ∧
      decoded out = DigestModelDecomposition.suffixFold (SemanticPublicModel.exactPublic public1)
        (exactOpenings openings) (pointSelector point) (decoded initial) := by
  obtain ⟨out, ho, hco, hvo⟩ := source_success point selectors initial openings.z public1
    hpoint hbox hinitial hopened hroot hfrontier
  exact ⟨out, ho, hco, hvo.trans (model_eq_r0p point openings public1 (decoded initial))⟩

#print axioms model_eq_r0p
#print axioms source_success_r0p
end
end AspisR1.DigestWrapperSuffix.R0PBridge
