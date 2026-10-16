import ValueLaneEnclosingSlice
import ValueLaneCompleteProgram

/-! Bind the actual generated enclosing candidate declaration to the proved
complete value-family program. Canonical input openings derive the three loop
successes and preserve the original openings across the generated tuple flow.
-/
set_option autoImplicit false
namespace AspisR1.ValueLaneEnclosingBridge
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

theorem enclosing_eq_program
    (selectors : Selectors) (packed : Array QM 24#usize) (openings : Openings)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z) :
    AspisR1ValueLaneCandidate.pool_v1.pair_forest_semantic_terminal.add_value_lanes
      packed openings selectors =
        AspisR1.ValueLaneCompleteProgram.run selectors packed openings := by
  obtain ⟨openings3, range1, range2, range3, h0, h1, h2, hopen, _hcanonical⟩ :=
    AspisR1.SelectorValueLanePreprocessExecution.preprocessing_success_canonical
      openings hz hsucc hxor
  subst openings3
  unfold AspisR1ValueLaneCandidate.pool_v1.pair_forest_semantic_terminal.add_value_lanes
    AspisR1.ValueLaneCompleteProgram.run
    AspisR1.ValueLaneRangeSelectorRun.run AspisR1.SelectorValueLaneMap.selectorIndices
    AspisR1.SelectorValueLaneRangeConstruction.rangeConstruction
    AspisR1.SelectorValueLaneFullRangeValues.rangePrefixConstruction
    AspisR1.SelectorValueLaneTailExecution.tailConstruction
    AspisR1.ValueLaneSourceComposition.run
    AspisR1.SelectorConservationSourceIndex.run
    AspisR1.SelectorConservationSourceIndex.selectorIndex
    AspisR1.ValueConservationTail.run
  simp only [bind_assoc, h0, h1, h2, bind_tc_ok]

theorem actual_enclosing_valueFamily
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (openings : Openings)
    (pub : R0P.Public ExactQM) (pub' : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z) :
    ∃ out : Array QM 24#usize,
      AspisR1ValueLaneCandidate.pool_v1.pair_forest_semantic_terminal.add_value_lanes
        packed openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 ((R0P.valueFamily (K := Wide)).residuals pub'
              (mapOpenings f (exactOpenings openings))
              (fun i => f (pointSelector point i))) (4*j.val+k.val)) := by
  have hcomplete := AspisR1.ValueLaneCompleteProgram.same_boxed_complete_valueFamily
    point selectors packed openings pub pub' hpoint hbox hpacked hz hsucc hxor
  obtain ⟨out, hrun, hcanonical, hvalue⟩ := hcomplete
  refine ⟨out, ?_, hcanonical, ?_⟩
  · exact (enclosing_eq_program selectors packed openings hz hsucc hxor).trans hrun
  · simpa only [AspisR1.ValueLaneCompleteProgram.exactOpenings, exactOpenings] using hvalue

#print axioms enclosing_eq_program
#print axioms actual_enclosing_valueFamily
end
end AspisR1.ValueLaneEnclosingBridge
