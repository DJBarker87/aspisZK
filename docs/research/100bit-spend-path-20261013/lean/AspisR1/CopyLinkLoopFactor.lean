import AspisR1.CopyLinkLoopCandidate
import AspisR1.CopyLinkStepExact
import AspisR1.ResultPairSequence

/-! Exact factoring of one actual Copy loop iteration through the proved
weight/producer/consumer step. The registry read is still the actual source read. -/
set_option autoImplicit false
namespace AspisR1.CopyLinkLoopFactor
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyLinkWeightExact AspisR1.CopyLinkStepExact
abbrev loopFn := AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop
abbrev registry := AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS
abbrev count := AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1

theorem loop_step_eq (selectors : Selectors) (index : U64) (variant : Variant)
    (patterns : Array QM 14#usize) (pv pw cv cw : Array QM 2#usize)
    (cursor : Usize) (link : Raw)
    (hlt : cursor < count) (hread : Array.index_usize registry cursor = .ok link) :
    loopFn selectors index variant patterns pv pw cv cw cursor = (do
      let (pv1,pw1,cv1,cw1) ← runStep link index variant patterns selectors pv pw cv cw
      let cursor1 ← cursor + 1#usize
      loopFn selectors index variant patterns pv1 pw1 cv1 cw1 cursor1) := by
  unfold loopFn
  rw [AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop.eq_def]
  simp only [hlt, if_pos, hread, bind_tc_ok]
  exact AspisR1.ResultPairSequence.three_pair_bind
    (weightFn link index variant)
    (fun weight => AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.accumulate_endpoint
      pv pw link.producer link.tag weight patterns selectors)
    (fun weight => AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.accumulate_endpoint
      cv cw link.consumer link.tag weight patterns selectors)
    (fun pv1 pw1 cv1 cw1 => do
      let cursor1 ← cursor + 1#usize
      loopFn selectors index variant patterns pv1 pw1 cv1 cw1 cursor1)

#print axioms loop_step_eq
end AspisR1.CopyLinkLoopFactor
