import SumHighBoxedModel

/-! Exact `poseidon_selectors` field projection and singleton high range. The
output uses the exact StateOnlyPoseidonSelectors declaration absent from the
selected base Types object; the source cut extends that same namespace. -/
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
-- Exact missing carrier declaration cut from the sealed generated Types.
structure state_only_poseidon.StateOnlyPoseidonSelectors where
  block : field.QM31
  «local» : Aeneas.Std.Array field.QM31 16#usize
end AspisR1SelectedMaskProbe

namespace AspisR1.PoseidonSelectorsSource
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

abbrev Output := state_only_poseidon.StateOnlyPoseidonSelectors

def source (selectors : Selectors) : Result Output := do
  let ranges ← lift (Array.to_slice
    (Array.make 1#usize [({ start := 0#usize, «end» := 57#usize } : Range)]))
  let block ← AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high selectors ranges
  .ok { block := block, «local» := selectors.low }

/-- Same actual boxed point supplies both the source high-range sum and every
low marginal. No block/low model equation is an independent premise. -/
theorem boxed_success
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ out : Output, source selectors = .ok out ∧ Canonical out.block ∧
      CanonicalArray out.«local» ∧ out.«local» = selectors.low ∧
      decode out.block = R0P.g2SumHigh (pointSelector point) 0 57 (by omega) ∧
      ∀ i : Fin 16, AspisR1.SelectorExpansionCorrectness.decodedArray out.«local» i.val =
        R0P.g2Low (pointSelector point) i := by
  let r : Range := { start := 0#usize, «end» := 57#usize }
  obtain ⟨block,hrun,hcanonical,hmodel⟩ :=
    AspisR1.SumHighBoxedModel.boxed_singleton point selectors r hpoint hbox
      (by dsimp [r]; scalar_tac) (by dsimp [r]; scalar_tac)
  obtain ⟨_,hlow,_,hlowModel⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  refine ⟨{ block := block, «local» := selectors.low },?_,hcanonical,hlow,rfl,?_,hlowModel⟩
  · change (do
      let ranges ← lift (Array.to_slice (Array.make 1#usize [r]))
      let b ← AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high selectors ranges
      .ok ({ block := b, «local» := selectors.low } : Output)) = _
    change (do
      let b ← AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
        selectors (AspisR1.SumHighSingleRange.singleton r)
      .ok ({ block := b, «local» := selectors.low } : Output)) = _
    rw [hrun]
    rfl
  · have h0 : (0#usize).val = 0 := by scalar_tac
    have h57 : (57#usize).val = 57 := by scalar_tac
    simpa only [r,h0,h57,Nat.sub_zero] using hmodel

#print axioms boxed_success
end
end AspisR1.PoseidonSelectorsSource
