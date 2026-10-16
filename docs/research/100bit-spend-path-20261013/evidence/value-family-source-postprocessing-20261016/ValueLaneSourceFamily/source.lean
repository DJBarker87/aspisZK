import ValueLaneSourceComposition

/-! Source value-family endpoint. Canonical point/opening inputs and the
weighted range identification suffice; the conservation residuals, all source
packing operations and the exact WideExact relation are derived here. -/
set_option autoImplicit false
namespace AspisR1.ValueLaneSourceFamily
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneResidualList
open AspisR1.ValueLaneExactResidualBridge
open AspisR1.SelectorConservationTail
open AspisR1.ValueFamilyFieldTransport

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

theorem same_boxed_valueFamily
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (values : Array QM 33#usize)
    (z succ : Array QM 16#usize)
    (pub : R0P.Public ExactQM) (pub' : R0P.Public Wide)
    (o : R0P.Openings ExactQM)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values)
    (hz : CanonicalArray z) (hsucc : CanonicalArray succ)
    (hzmodel : ∀ i : Fin 16,
      AspisR1.ExtractedMaskQM31Exact.decode (AspisR1.ValueConservationTail.cellAt z i) = o.z i)
    (hsuccmodel : ∀ i : Fin 16,
      AspisR1.ExtractedMaskQM31Exact.decode (AspisR1.ValueConservationTail.cellAt succ i) = o.succ i)
    (hrange : List.ofFn (exactVector values) =
      (R0P.valueRange o).map (fun r =>
        AspisR1.SelectorValueLaneModelComposition.valueFamilyCoefficientFor
          (pointSelector point) * r)) :
    ∃ out : Array QM 24#usize,
      AspisR1.ValueLaneSourceComposition.run selectors packed values z succ = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 ((R0P.valueFamily (K := Wide)).residuals pub'
              (mapOpenings f o) (fun i => f (pointSelector point i))) (4*j.val+k.val)) := by
  obtain ⟨conservation, out, hrun, hout, _hconservation, hlist, hmodel⟩ :=
    AspisR1.ValueLaneSourceComposition.same_boxed_run_list
      point selectors packed values z succ hpoint hbox hpacked hvalues hz hsucc
  have hcons : List.ofFn (exactVector conservation) =
      [pointSelector point 1014 * ((o.z 0-o.z 1)-o.z 2),
       pointSelector point 1014 * (o.succ 0-o.succ 1)] := by
    simpa only [hzmodel, hsuccmodel] using hlist
  have hexact := AspisR1.ConservationResidualIdentification.exactResiduals_of_components
    values conservation pub o (pointSelector point) hrange hcons
  have hwide := residuals_valueFamily
    values conservation pub pub' o (pointSelector point) hexact
  exact ⟨out, hrun, hout, by simpa only [hwide] using hmodel⟩

#print axioms same_boxed_valueFamily
end
end AspisR1.ValueLaneSourceFamily
