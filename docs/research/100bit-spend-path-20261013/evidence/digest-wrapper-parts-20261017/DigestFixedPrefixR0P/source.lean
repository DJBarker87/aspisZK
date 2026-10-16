import DigestFixedPrefixSource
import DigestModelDecomposition
import SelectorValueLanePreprocessRangeValues

set_option autoImplicit false
namespace AspisR1.DigestFixedPrefix.R0PBridge
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
open AspisR1.DigestFixedBinding
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings

theorem opened_model (openings : Openings) :
    openedModel openings.z = (exactOpenings openings).z := by
  funext j
  have hj : j.val < openings.z.val.length := by
    simpa [openings.z.property] using j.isLt
  unfold openedModel openedAt exactOpenings
    AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
  rw [List.getElem?_eq_getElem hj]
  rfl

attribute [local irreducible] R0P.digestAddBinding
  AspisR1.SelectorValueLaneModelComposition.pointSelector

/-- The prefix model uses the same public value and opened values as the old
complete digest relation, including optional recipient presence. -/
theorem model_eq_r0p (point : Array QM 10#usize) (openings : Openings) (public1 : Public) :
    model point openings.z public1 =
      DigestModelDecomposition.prefixFold (SemanticPublicModel.exactPublic public1)
        (exactOpenings openings) (pointSelector point) := by
  cases hrec : public1.recipient <;>
    simp only [model, step, DigestModelDecomposition.prefixFold,
      DigestModelDecomposition.prefixKeys, DigestModelDecomposition.foldStep,
      SemanticPublicModel.exactPublic, hrec, Option.map, Option.getD,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      R0P.digestRow, R0P.digestStart, R0P.digestTarget]
  all_goals rw [← opened_model]
  all_goals rfl

/-- Actual original source prefix, same public and openings, with every
operation success derived from canonical inputs and the boxed selector. -/
theorem exactPrefix_success (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hopened : CanonicalArray openings.z)
    (ha : DigestWordsCanonical public1.anchor)
    (hn : DigestWordsCanonical public1.nullifier)
    (hc : DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → DigestWordsCanonical recipient) :
    ∃ out, Source.exactPrefix public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      decoded out = DigestModelDecomposition.prefixFold (SemanticPublicModel.exactPublic public1)
        (exactOpenings openings) (pointSelector point) := by
  obtain ⟨out, ho, hco, hvo⟩ := source_success point selectors public1 openings.z
    hpoint hbox hopened ha hn hc hr
  refine ⟨out, ?_, hco, ?_⟩
  · rw [Source.exactPrefix_eq_factored]
    exact ho
  · rw [hvo, model_eq_r0p]

#print axioms opened_model
#print axioms model_eq_r0p
#print axioms exactPrefix_success
end
end AspisR1.DigestFixedPrefix.R0PBridge
