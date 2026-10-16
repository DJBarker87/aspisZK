import PathLaneEnclosingSlice
import PathLaneCompleteProgram

/-! Bind the whole generated enclosing add_path_lanes candidate to the full
proved path-family program, retaining its exact selector prefix and openings. -/
set_option autoImplicit false
namespace AspisR1.PathLaneEnclosingBridge
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev exactOpenings := AspisR1.PathLaneCompleteProgram.exactOpenings

theorem enclosing_eq_program (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (packed : Array QM 24#usize) (openings : Openings) :
    AspisR1PathEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_path_lanes
      packed openings selectors = AspisR1.PathLaneCompleteProgram.run selectors packed openings := by
  unfold AspisR1PathEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_path_lanes
    AspisR1.PathLaneCompleteProgram.run AspisR1.PathSelectorPrefix.run
    AspisR1.PathSelectorPrefix.runLow AspisR1.PathLanePacking.run
    AspisR1.SumHighSingleRange.singleton AspisR1.SumHighBoxedModel.pathRange
  simp only [lift, bind_tc_ok, bind_assoc]

theorem actual_enclosing_pathFamily
    (point : Array QM 10#usize) (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (packed : Array QM 24#usize) (openings : Openings) (pub : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z) :
    ∃ out : Array QM 24#usize,
      AspisR1PathEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_path_lanes
        packed openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 => selectList 32
            ((R0P.pathFamily (K := Wide)).residuals pub
              (mapOpenings f (exactOpenings openings))
              (fun i => f (pointSelector point i))) (4*j.val+k.val)) := by
  have hcomplete := AspisR1.PathLaneCompleteProgram.same_boxed_complete_pathFamily
    point selectors packed openings pub hpoint hbox hpacked hz hsucc
  obtain ⟨out, hrun, hcanonical, hvalue⟩ := hcomplete
  refine ⟨out, (enclosing_eq_program selectors packed openings).trans hrun, hcanonical, ?_⟩
  simpa only [AspisR1.PathLaneCompleteProgram.exactOpenings, exactOpenings] using hvalue

#print axioms enclosing_eq_program
#print axioms actual_enclosing_pathFamily
end
end AspisR1.PathLaneEnclosingBridge
