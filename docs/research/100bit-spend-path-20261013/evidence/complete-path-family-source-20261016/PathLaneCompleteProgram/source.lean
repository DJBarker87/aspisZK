import PathSelectorPrefix
import PathLanePacking

/-! Full path-family program with its selector prefix and literal/packing
calls on the same boxed point and source openings. -/
set_option autoImplicit false
namespace AspisR1.PathLaneCompleteProgram
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
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev exactOpenings := AspisR1.PathLanePacking.exactOpenings

def run (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (packed : Array QM 24#usize) (openings : Openings) : Result (Array QM 24#usize) := do
  let selector ← AspisR1.PathSelectorPrefix.run selectors
  AspisR1.PathLanePacking.run packed selector openings

theorem same_boxed_complete_pathFamily
    (point : Array QM 10#usize) (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (packed : Array QM 24#usize) (openings : Openings) (pub : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z) :
    ∃ out : Array QM 24#usize, run selectors packed openings = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 => selectList 32
            ((R0P.pathFamily (K := Wide)).residuals pub
              (mapOpenings f (exactOpenings openings))
              (fun i => f (pointSelector point i))) (4*j.val+k.val)) := by
  obtain ⟨selector, hselectorRun, hselectorCanonical, hselectorValue⟩ :=
    AspisR1.PathSelectorPrefix.boxed_path_selector point selectors hpoint hbox
  obtain ⟨out, hpack, hcanonical, hmodel⟩ :=
    AspisR1.PathLanePacking.run_pathLanes packed selector openings hpacked hselectorCanonical hz hsucc
  have hselectorWide : f (AspisR1.ExtractedMaskQM31Exact.decode selector) =
      R0P.pathSelector (fun i => f (pointSelector point i)) := by
    have hmap := congrArg (fun x : ExactQM => f x) hselectorValue
    exact hmap.trans (AspisR1.PathFamilyFieldTransport.map_selector f (pointSelector point))
  refine ⟨out, ?_, hcanonical, ?_⟩
  · simp only [run, hselectorRun, bind_tc_ok, hpack]
  · simpa only [hselectorWide, R0P.pathFamily] using hmodel

#print axioms same_boxed_complete_pathFamily
end
end AspisR1.PathLaneCompleteProgram
