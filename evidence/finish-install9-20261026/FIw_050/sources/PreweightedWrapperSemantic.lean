import PreweightedWrapperModel
import ExtractedMaskQmPackBase4Semantic

/-! End-to-end actual packed-interval primitive to the retained WideExact/R0P
four-lane packing formula, reusing the proved exact-tower embedding. -/
set_option autoImplicit false
namespace AspisR1.PreweightedWrapperSemantic
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic

theorem add_preweighted_semantic {N : Usize}
    (packed : Array QM 24#usize) (start : Usize) (values : Array QM N)
    (hn : 0 < N.val) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed start values = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            f (AspisR1.ExtractedMaskQM31Exact.decode
              (selectedCell values start.val j.val k.val))) := by
  obtain ⟨out, hrun, hcanon, hmodel⟩ :=
    AspisR1.PreweightedWrapperModel.add_preweighted_model
      packed start values hn hinterval hpacked hvalues
  refine ⟨out, hrun, hcanon, ?_⟩
  intro j
  have hj := congrArg (fun a : State => a j) hmodel
  change decoded out j = decoded packed j + groupValue values start.val j.val at hj
  rw [hj, map_add, groupValue, map_mathPack]

#print axioms add_preweighted_semantic
end
end AspisR1.PreweightedWrapperSemantic
