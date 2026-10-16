import PreweightedWrapperSemantic

/-! Composition of the two actual packed-interval calls in add_value_lanes.
The source intervals overlap in one packed group, so their lane contributions
must be added before identifying the complete value-family packed residual. -/
set_option autoImplicit false
namespace AspisR1.ValueLanePackedComposition
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic

/-- Generic linearity keeps the proof symbolic in the field and basis. -/
theorem pack_add {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) (a b : Fin 4 → K) :
    R0P.pack4 B (fun j => a j + b j) = R0P.pack4 B a + R0P.pack4 B b := by
  unfold R0P.pack4
  ring

def run (packed : Array QM 24#usize) (range : Array QM 33#usize)
    (conservation : Array QM 2#usize) : Result (Array QM 24#usize) := do
  let packed1 ←
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
      packed 49#usize range
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    packed1 82#usize conservation

theorem run_semantic (packed : Array QM 24#usize) (range : Array QM 33#usize)
    (conservation : Array QM 2#usize)
    (hpacked : CanonicalArray packed) (hrange : CanonicalArray range)
    (hconservation : CanonicalArray conservation) :
    ∃ packed1 out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed 49#usize range = .ok packed1 ∧
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed1 82#usize conservation = .ok out ∧
      run packed range conservation = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            f (AspisR1.ExtractedMaskQM31Exact.decode
              (selectedCell range 49 j.val k.val)) +
            f (AspisR1.ExtractedMaskQM31Exact.decode
              (selectedCell conservation 82 j.val k.val))) := by
  obtain ⟨packed1, hfirst, hcanonical1, hmodel1⟩ :=
    AspisR1.PreweightedWrapperSemantic.add_preweighted_semantic
      packed 49#usize range (by decide) (by decide) hpacked hrange
  obtain ⟨out, hsecond, hcanonicalOut, hmodel2⟩ :=
    AspisR1.PreweightedWrapperSemantic.add_preweighted_semantic
      packed1 82#usize conservation (by decide) (by decide) hcanonical1 hconservation
  have h49 : (49#usize).val = 49 := by scalar_tac
  have h82 : (82#usize).val = 82 := by scalar_tac
  simp only [h49] at hmodel1
  simp only [h82] at hmodel2
  refine ⟨packed1, out, hfirst, hsecond, ?_, hcanonicalOut, ?_⟩
  · simp only [run, hfirst, bind_tc_ok, hsecond]
  · intro j
    rw [hmodel2, hmodel1, pack_add, add_assoc]

#print axioms pack_add
#print axioms run_semantic
end
end AspisR1.ValueLanePackedComposition
