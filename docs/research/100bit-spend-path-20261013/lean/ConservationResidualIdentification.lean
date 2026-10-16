import SelectorConservationSourceIndex
import ValueLaneExactResidualBridge

/-! The conservation array constructed by the actual source is exactly the
two-entry residual-list tail. Together with the weighted range list this
discharges the full value-family residual identification. -/
set_option autoImplicit false
namespace AspisR1.ConservationResidualIdentification
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.SelectorConservationTail
open AspisR1.ValueLaneExactResidualBridge

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

theorem same_boxed_source_residual_list
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (z succ : Array QM 16#usize)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point =
      .ok selectors)
    (hpacked : CanonicalArray packed) (hz : CanonicalArray z)
    (hsucc : CanonicalArray succ) :
    ∃ selector r0 r1 : QM, ∃ out : Array QM 24#usize,
      AspisR1.SelectorConservationSourceIndex.run selectors packed z succ = .ok out ∧
      CanonicalArray out ∧ CanonicalArray (Array.make 2#usize [r0, r1]) ∧
      decoded out = (fun j => decoded packed j +
        groupValue (Array.make 2#usize [r0, r1]) 82 j.val) ∧
      decode selector = pointSelector point 1014 ∧
      List.ofFn (exactVector (Array.make 2#usize [r0, r1])) =
        [pointSelector point 1014 *
          ((decode (AspisR1.ValueConservationTail.cellAt z 0) -
            decode (AspisR1.ValueConservationTail.cellAt z 1)) -
              decode (AspisR1.ValueConservationTail.cellAt z 2)),
         pointSelector point 1014 *
          (decode (AspisR1.ValueConservationTail.cellAt succ 0) -
            decode (AspisR1.ValueConservationTail.cellAt succ 1))] := by
  obtain ⟨selector, r0, r1, out, hrun, hout, harray, hmodel, hselector, hv0, hv1⟩ :=
    AspisR1.SelectorConservationSourceIndex.same_boxed_source_tail
      point selectors packed z succ hpoint hbox hpacked hz hsucc
  refine ⟨selector, r0, r1, out, hrun, hout, harray, hmodel, hselector, ?_⟩
  change [decode r0, decode r1] = _
  rw [hv0, hv1]

theorem exactResiduals_of_components
    (range : Array QM 33#usize) (conservation : Array QM 2#usize)
    (pub : R0P.Public ExactQM) (o : R0P.Openings ExactQM) (sel : R0P.Sel ExactQM)
    (hrange : List.ofFn (exactVector range) =
      (R0P.valueRange o).map (fun r =>
        AspisR1.SelectorValueLaneModelComposition.valueFamilyCoefficientFor sel * r))
    (hconservation : List.ofFn (exactVector conservation) =
      [sel 1014 * ((o.z 0-o.z 1)-o.z 2), sel 1014 * (o.succ 0-o.succ 1)]) :
    exactResiduals range conservation =
      (R0P.valueFamily (K := ExactQM)).residuals pub o sel := by
  rw [exactResiduals, hrange, hconservation]
  exact (AspisR1.SelectorValueLaneModelComposition.valueFamily_uses_rangeCoefficient_for
    sel pub o).symm

#print axioms same_boxed_source_residual_list
#print axioms exactResiduals_of_components
end
end AspisR1.ConservationResidualIdentification
