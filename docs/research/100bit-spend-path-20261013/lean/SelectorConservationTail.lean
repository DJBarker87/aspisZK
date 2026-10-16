import SelectorValueLaneModelComposition
import ValueConservationTail

/-! The conservation selector and arithmetic tail use the same actual boxed
point as the range selector. The generated row call and all subsequent reads,
field operations and packing succeed from canonical inputs. -/
set_option autoImplicit false
namespace AspisR1.SelectorConservationTail
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ValueConservationTail

abbrev QM := field.QM31
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Canonical := CurrentCanonicalQM

theorem same_boxed_conservation_selector
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point =
      .ok selectors) :
    ∃ selector : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors 1014#usize =
        .ok selector ∧ Canonical selector ∧
      decode selector = pointSelector point 1014 := by
  obtain ⟨selectors', selector, hbox', hrow, hcanonical, hvalue⟩ :=
    AspisR1.SelectorRowCall.boxed_row_matches_ten_factor point hpoint
      1014#usize (by scalar_tac)
  have hsame : selectors' = selectors := Result.ok.inj (hbox'.symm.trans hbox)
  subst selectors'
  refine ⟨selector, hrow, hcanonical, ?_⟩
  have h1014 : (1014#usize).val = 1014 := by scalar_tac
  change decode selector = AspisV8.SelectedSelectorExpansion.tensorProduct
    (AspisR1.SelectorAtPointModel.exactPoint point) 10 1014
  simpa only [h1014] using hvalue

theorem same_boxed_conservation_tail
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (z succ : Array QM 16#usize)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point =
      .ok selectors)
    (hpacked : CanonicalArray packed) (hz : CanonicalArray z)
    (hsucc : CanonicalArray succ) :
    ∃ selector r0 r1 : QM, ∃ out : Array QM 24#usize,
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors 1014#usize =
        .ok selector ∧ Canonical selector ∧
      decode selector = pointSelector point 1014 ∧
      run packed selector z succ = .ok out ∧ CanonicalArray out ∧
      CanonicalArray (Array.make 2#usize [r0, r1]) ∧
      decoded out = (fun j => decoded packed j +
        groupValue (Array.make 2#usize [r0, r1]) 82 j.val) ∧
      decode r0 = pointSelector point 1014 *
        ((decode (cellAt z 0) - decode (cellAt z 1)) - decode (cellAt z 2)) ∧
      decode r1 = pointSelector point 1014 *
        (decode (cellAt succ 0) - decode (cellAt succ 1)) := by
  obtain ⟨selector, hrow, hselector, hvalue⟩ :=
    same_boxed_conservation_selector point selectors hpoint hbox
  obtain ⟨r0, r1, out, hrun, hout, harray, hmodel, hv0, hv1⟩ :=
    run_success packed selector z succ hpacked hselector hz hsucc
  refine ⟨selector, r0, r1, out, hrow, hselector, hvalue, hrun, hout,
    harray, hmodel, ?_, ?_⟩
  · simpa only [hvalue] using hv0
  · simpa only [hvalue] using hv1

#print axioms same_boxed_conservation_selector
#print axioms same_boxed_conservation_tail
end AspisR1.SelectorConservationTail
