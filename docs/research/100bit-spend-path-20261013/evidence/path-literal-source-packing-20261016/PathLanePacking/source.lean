import PathLaneListCorrespondence
import PathFamilyFieldTransport
import PreweightedListSemantic

/-! The actual path residual construction followed by actual start32 packing.
The earlier enclosing selector-prefix call remains separate. -/
set_option autoImplicit false
namespace AspisR1.PathLanePacking
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport

abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev exactOpenings := AspisR1.PathLaneListCorrespondence.exactOpenings

def run (packed : Array QM 24#usize) (selector : QM) (openings : Openings) :
    Result (Array QM 24#usize) := do
  let values ← AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal
    selector openings
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    packed 32#usize values

theorem run_pathLanes (packed : Array QM 24#usize) (selector : QM) (openings : Openings)
    (hpacked : CanonicalArray packed) (hs : Canonical selector)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z) :
    ∃ out : Array QM 24#usize, run packed selector openings = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 => selectList 32
            (R0P.pathLanes (f (AspisR1.ExtractedMaskQM31Exact.decode selector))
              (mapOpenings f (exactOpenings openings))) (4*j.val+k.val)) := by
  obtain ⟨values, hvaluesRun, hvaluesCanonical, hvaluesList⟩ :=
    AspisR1.PathLaneListCorrespondence.literal_list selector openings hs hz hsucc
  have hlist : List.ofFn (arrayVector values) =
      R0P.pathLanes (f (AspisR1.ExtractedMaskQM31Exact.decode selector))
        (mapOpenings f (exactOpenings openings)) := by
    have hmap : List.ofFn (arrayVector values) =
        (List.ofFn (AspisR1.PathLaneListCorrespondence.exactVector values)).map f := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, hvaluesList]
    exact AspisR1.PathFamilyFieldTransport.map_lanes f
      (AspisR1.ExtractedMaskQM31Exact.decode selector) (exactOpenings openings)
  obtain ⟨out, hpack, hcanonical, hmodel⟩ :=
    AspisR1.PreweightedListSemantic.add_preweighted_residual_list
      packed 32#usize values _ (by scalar_tac) (by scalar_tac)
      hpacked hvaluesCanonical hlist
  refine ⟨out, ?_, hcanonical, ?_⟩
  · simp only [run, hvaluesRun, bind_tc_ok, hpack]
  · have h32 : (32#usize).val = 32 := by scalar_tac
    simpa only [h32] using hmodel

#print axioms run_pathLanes
end
end AspisR1.PathLanePacking
