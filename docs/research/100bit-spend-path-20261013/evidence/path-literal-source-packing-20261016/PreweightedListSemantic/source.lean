import PreweightedWrapperSemantic
import ValueLaneResidualList

/-! Reusable source packing endpoint in the retained residual-list form.
Every family can supply its proved list identity without reproving padding,
field transport, framing or checked source packing. -/
set_option autoImplicit false
namespace AspisR1.PreweightedListSemantic
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList

theorem add_preweighted_list {N : Usize}
    (packed : Array QM 24#usize) (start : Usize) (values : Array QM N)
    (hn : 0 < N.val) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed start values = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList start.val (List.ofFn (arrayVector values)) (4*j.val+k.val)) := by
  obtain ⟨out, hrun, hcanonical, hvalues⟩ :=
    AspisR1.PreweightedWrapperSemantic.add_preweighted_semantic
      packed start values hn hinterval hpacked hvalues
  refine ⟨out, hrun, hcanonical, ?_⟩
  intro j
  rw [hvalues j]
  congr 1
  congr 1
  funext k
  rw [selectedCell_vector, selectList_ofFn]

theorem add_preweighted_residual_list {N : Usize}
    (packed : Array QM 24#usize) (start : Usize) (values : Array QM N)
    (residuals : List Wide)
    (hn : 0 < N.val) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values)
    (hresiduals : List.ofFn (arrayVector values) = residuals) :
    ∃ out : Array QM 24#usize,
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed start values = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList start.val residuals (4*j.val+k.val)) := by
  obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
    add_preweighted_list packed start values hn hinterval hpacked hvalues
  exact ⟨out, hrun, hcanonical, by simpa only [hresiduals] using hmodel⟩

#print axioms add_preweighted_list
#print axioms add_preweighted_residual_list
end
end AspisR1.PreweightedListSemantic
