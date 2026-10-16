import ConservationResidualIdentification

/-! Actual source composition after the weighted range is constructed:
start49 packing, the same point's conservation selector, source arithmetic,
and start82 packing. The returned source result is tied to one residual list.
-/
set_option autoImplicit false
namespace AspisR1.ValueLaneSourceComposition
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList
open AspisR1.ValueLaneExactResidualBridge
open AspisR1.ValueLaneIntervalJoin
open AspisR1.SelectorConservationTail

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def run (selectors : Selectors) (packed : Array QM 24#usize)
    (values : Array QM 33#usize) (z succ : Array QM 16#usize) :
    Result (Array QM 24#usize) := do
  let packed1 ←
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
      packed 49#usize values
  AspisR1.SelectorConservationSourceIndex.run selectors packed1 z succ

theorem selected_list (range : Array QM 33#usize) (conservation : Array QM 2#usize)
    (group slot : Nat) :
    selectList 49 (sourceResiduals range conservation) (4*group+slot) =
      f (AspisR1.ExtractedMaskQM31Exact.decode (selectedCell range 49 group slot)) +
      f (AspisR1.ExtractedMaskQM31Exact.decode
        (selectedCell conservation 82 group slot)) := by
  rw [sourceResiduals, ← ofFn_appendVector, selectList_ofFn, selectVector_append]
  have hstart : 49 + (33#usize).val = 82 := by scalar_tac
  rw [hstart, ← selectedCell_vector, ← selectedCell_vector]

theorem same_boxed_run_list
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (values : Array QM 33#usize)
    (z succ : Array QM 16#usize)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values)
    (hz : CanonicalArray z) (hsucc : CanonicalArray succ) :
    ∃ conservation : Array QM 2#usize, ∃ out : Array QM 24#usize,
      run selectors packed values z succ = .ok out ∧ CanonicalArray out ∧
      CanonicalArray conservation ∧
      List.ofFn (exactVector conservation) =
        [pointSelector point 1014 *
          ((AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.ValueConservationTail.cellAt z 0) -
            AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.ValueConservationTail.cellAt z 1)) -
            AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.ValueConservationTail.cellAt z 2)),
         pointSelector point 1014 *
          (AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.ValueConservationTail.cellAt succ 0) -
            AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.ValueConservationTail.cellAt succ 1))] ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 (sourceResiduals values conservation) (4*j.val+k.val)) := by
  obtain ⟨packed1, hfirst, hcanonical1, hmodel1⟩ :=
    AspisR1.PreweightedWrapperSemantic.add_preweighted_semantic
      packed 49#usize values (by decide) (by decide) hpacked hvalues
  obtain ⟨selector, r0, r1, out, htail, hout, harray, hmodel2, _hselector, hlist⟩ :=
    AspisR1.ConservationResidualIdentification.same_boxed_source_residual_list
      point selectors packed1 z succ hpoint hbox hcanonical1 hz hsucc
  refine ⟨Array.make 2#usize [r0, r1], out, ?_, hout, harray, hlist, ?_⟩
  · simp only [run, hfirst, bind_tc_ok, htail]
  · intro j
    have hj := congrArg (fun a : State => f (a j)) hmodel2
    change f (decoded out j) =
      f (decoded packed1 j + groupValue (Array.make 2#usize [r0, r1]) 82 j.val) at hj
    rw [map_add, groupValue, map_mathPack] at hj
    rw [hj, hmodel1]
    have h49 : (49#usize).val = 49 := by scalar_tac
    simp only [h49]
    simp_rw [selected_list]
    rw [AspisR1.ValueLanePackedComposition.pack_add, add_assoc]

#print axioms selected_list
#print axioms same_boxed_run_list
end
end AspisR1.ValueLaneSourceComposition
