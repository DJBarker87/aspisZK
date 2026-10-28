import R1Z.PV_RunJoin_LaneABI31
import R1Z.PV_RunJoin_LaneDenotation31
import R1Z.PV_RunJoin_LaneOrientation31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneNative31
open Aeneas Aeneas.Std Result
variable [BuilderForestAdmissionPort.ExternalLinear]

theorem complete_result
    (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) :
    PV_RunJoin_LaneABI31.call x =
      (do let r ← PV_RunJoin_LaneDenotation31.model (PV_RunJoin_LaneABI31.fromOuter x)
          ok (match r with | .Ok d => .Ok d | .Err e => .Err (PV_RunJoin_LaneABI31.errorToOuter e))) := by
  unfold PV_RunJoin_LaneABI31.call
  rw [PV_RunJoin_LaneDenotation31.complete_result]
#print axioms complete_result

theorem installed
    (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) :
    @PV_RunJoin_Outer30.pool_v1.pair_forest_trace.lane_root PV_RunJoin_LaneABI31.native x =
      PV_RunJoin_LaneABI31.call x := rfl
#print axioms installed

theorem successful_root
    (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
    (root : Array U32 8#usize) (h : PV_RunJoin_LaneABI31.call x = ok (.Ok root)) :
    let input := PV_RunJoin_LaneABI31.fromOuter x
    ∃ d, PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest input.pair_leaf = ok (.Ok d) ∧
      PV_RunJoin_LaneFold31.fold
        PV_RunJoin_Lane31.aspis_statement.pool_v1.format.pool_v1_tree_parent
        (PV_RunJoin_LaneDenotation31.sibling input)
        (PV_RunJoin_LaneDenotation31.reverse input) (List.range 20) d = ok root := by
  unfold PV_RunJoin_LaneABI31.call at h
  obtain ⟨r,hr,ht⟩ := BuilderRecordsFields.bind_ok_inv h
  have hm := (PV_RunJoin_LaneDenotation31.complete_result
    (PV_RunJoin_LaneABI31.fromOuter x)).symm.trans hr
  cases r with
  | Err e => cases ht
  | Ok out =>
    cases Result.ok.inj ht
    exact (PV_RunJoin_LaneRecipe31.recipe_success _ _ _ _ _ _ _).mp hm
#print axioms successful_root
end R1Z.PV_RunJoin_LaneNative31
