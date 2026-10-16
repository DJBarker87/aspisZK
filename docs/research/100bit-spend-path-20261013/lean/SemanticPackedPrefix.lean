import ScheduleCompletePacking
import PathLaneEnclosingBridge
import ValueLaneEnclosingBridge
import OccupancyCompletePacking
import SemanticPublicModel

/-! The actual first four family calls in semantic_packed, starting at the
source's zero array. All success/canonicality/model premises are discharged. -/
set_option autoImplicit false
namespace AspisR1.SemanticPackedPrefix
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

def zero : Array QM 24#usize := Array.repeat 24#usize field.QM31.ZERO

theorem zero_canonical : CanonicalArray zero := by
  intro j
  change AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
    ((List.replicate 24 field.QM31.ZERO)[j.val]'(by simpa using j.isLt))
  rw [List.getElem_replicate]
  exact AspisR1.ExtractedMaskConstants.zero_canonical

theorem zero_decoded (j : Fin 24) : decoded zero j = 0 := by
  change AspisR1.ExtractedMaskQM31Exact.decode
    ((List.replicate 24 field.QM31.ZERO)[j.val]'(by simpa using j.isLt)) = 0
  rw [List.getElem_replicate]
  exact AspisR1.ExtractedMaskConstants.zero_decode

def run (public1 : Public) (openings : Openings) (selectors : Selectors) : Result (Array QM 24#usize) := do
  let packed1 ← AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
    zero public1 openings selectors
  let packed2 ← AspisR1PathEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_path_lanes
    packed1 openings selectors
  let packed3 ← AspisR1ValueLaneCandidate.pool_v1.pair_forest_semantic_terminal.add_value_lanes
    packed2 openings selectors
  pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes packed3 public1 openings selectors

@[irreducible] def familyContribution (family : R0P.Family Wide) (start : Nat)
    (pub : R0P.Public Wide) (o : R0P.Openings Wide) (sel : R0P.Sel Wide) (j : Fin 24) : Wide :=
  R0P.pack4 PackB (fun k : Fin 4 => selectList start (family.residuals pub o sel) (4*j.val+k.val))

@[irreducible] def model (pub : R0P.Public Wide) (o : R0P.Openings Wide)
    (sel : R0P.Sel Wide) (j : Fin 24) : Wide :=
  ((familyContribution R0P.scheduleFamily 0 pub o sel j + familyContribution R0P.pathFamily 32 pub o sel j) +
    familyContribution R0P.valueFamily 49 pub o sel j) + familyContribution R0P.occupancyFamily 0 pub o sel j

attribute [local irreducible] AspisR1.SelectorValueLaneModelComposition.pointSelector
  R0P.scheduleFamily R0P.pathFamily R0P.valueFamily R0P.occupancyFamily R0P.pack4
  AspisR1.ValueLaneResidualList.selectList

theorem source_success (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings) (pub : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z)
    (hv : pub.variant = (AspisR1.SemanticPublicModel.exactPublic public1).variant) :
    ∃ out, run public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) =
        model pub (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i)) j := by
  obtain ⟨packed1, h1, hc1, hm1⟩ := AspisR1.ScheduleCompletePacking.actual_enclosing_scheduleFamily
    point selectors zero public1 openings pub hpoint hbox zero_canonical hz hv
  obtain ⟨packed2, h2, hc2, hm2⟩ := AspisR1.PathLaneEnclosingBridge.actual_enclosing_pathFamily
    point selectors packed1 openings pub hpoint hbox hc1 hz hsucc
  obtain ⟨packed3, h3, hc3, hm3⟩ := AspisR1.ValueLaneEnclosingBridge.actual_enclosing_valueFamily
    point selectors packed2 openings (AspisR1.SemanticPublicModel.exactPublic public1) pub
    hpoint hbox hc2 hz hsucc hxor
  obtain ⟨out, h4, hc4, hm4⟩ := AspisR1.OccupancyCompletePacking.boxed_add_occupancy_lanes_success
    packed3 public1 openings point selectors pub hc3 hz hpoint hbox hv
  have hfamily := AspisR1.OccupancyCompletePacking.wideOccupancyFamily_residuals_eq pub
    (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i))
  rw [hfamily] at hm4
  refine ⟨out, ?_, hc4, ?_⟩
  · simp only [run, h1, bind_tc_ok, h2, h3, h4]
  · intro j
    unfold model familyContribution
    rw [hm4 j, hm3 j, hm2 j, hm1 j, zero_decoded, map_zero, zero_add]

#print axioms zero_canonical
#print axioms zero_decoded
#print axioms source_success
end
end AspisR1.SemanticPackedPrefix
