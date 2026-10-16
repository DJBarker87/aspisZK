import ValueLaneSourceFamily
import ValueLaneRangeSelectorRun
import SelectorValueLaneRangeConstruction

/-! Complete factored value-family candidate program. The exact source
selector prefix, range construction and postprocessing run on the same input
openings and boxed selectors. There is no residual-construction premise. The
remaining integration is correspondence with the generated enclosing caller.
-/
set_option autoImplicit false
namespace AspisR1.ValueLaneCompleteProgram
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport
open AspisR1.SelectorConservationTail

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings

def run (selectors : Selectors) (packed : Array QM 24#usize) (openings : Openings) :
    Result (Array QM 24#usize) := do
  let selector ← AspisR1.ValueLaneRangeSelectorRun.run selectors
  let values ← AspisR1.SelectorValueLaneRangeConstruction.rangeConstruction openings selector
  AspisR1.ValueLaneSourceComposition.run selectors packed values openings.z openings.succ_z

theorem same_boxed_complete_valueFamily
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (openings : Openings)
    (pub : R0P.Public ExactQM) (pub' : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z) :
    ∃ out : Array QM 24#usize,
      run selectors packed openings = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 ((R0P.valueFamily (K := Wide)).residuals pub'
              (mapOpenings f (exactOpenings openings))
              (fun i => f (pointSelector point i))) (4*j.val+k.val)) := by
  obtain ⟨selector, hselectorRun, hselectorCanonical, hselectorValue⟩ :=
    AspisR1.ValueLaneRangeSelectorRun.same_boxed_range_selector point selectors hpoint hbox
  obtain ⟨_preweighted, _hpreweighted, values, hvaluesRun, hvaluesCanonical, hvaluesList⟩ :=
    AspisR1.SelectorValueLaneRangeConstruction.rangeConstruction_weighted_list
      openings selector hz hsucc hxor hselectorCanonical
  have hlist : List.ofFn (AspisR1.ValueLaneExactResidualBridge.exactVector values) =
      (R0P.valueRange (exactOpenings openings)).map (fun r =>
        AspisR1.SelectorValueLaneModelComposition.valueFamilyCoefficientFor
          (pointSelector point) * r) := by
    simpa only [hselectorValue,
      AspisR1.SelectorValueLaneModelComposition.valueFamilyRangeCoefficient] using hvaluesList
  obtain ⟨out, hpost, houtCanonical, hmodel⟩ :=
    AspisR1.ValueLaneSourceFamily.same_boxed_valueFamily
      point selectors packed values openings.z openings.succ_z pub pub'
      (exactOpenings openings) hpoint hbox hpacked hvaluesCanonical hz hsucc
      (by intro i; rfl) (by intro i; rfl) hlist
  refine ⟨out, ?_, houtCanonical, hmodel⟩
  simp only [run, hselectorRun, bind_tc_ok, hvaluesRun, hpost]

#print axioms same_boxed_complete_valueFamily
end
end AspisR1.ValueLaneCompleteProgram
