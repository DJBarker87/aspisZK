import PoolS2_PlannerModel
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerCuts
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_Lanes PoolS2_PlannerModel

theorem accepted (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (plan : Plan)
    (h : run m lanes root bump = ok (.Ok plan)) :
    PoolS2_MasterValidation.run m = ok (.Ok ()) ∧
    m.initialized_lane_mask = 255#u8 ∧
    (∀ limb ∈ root.val, limb.val < 2147483647) ∧
    check m.identity.pool 0 lanes.val = .Ok () ∧
    ∃ pair : U8 × U64,
      PoolV_Chronology.chronology (Array.to_slice (sequences lanes))
        (Array.to_slice m.last_checkpoint_lane_sequences) m.has_checkpoint m.next_checkpoint_sequence = ok pair ∧
      pair.1 ≠ 1#u8 ∧ pair.1 ≠ 2#u8 ∧ pair.1 ≠ 3#u8 ∧
      PoolS2_MasterValidation.run (assembled m lanes root bump pair.2).next_master = ok (.Ok ()) ∧
      plan = assembled m lanes root bump pair.2 := by
  unfold run at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals aesop
  all_goals scalar_tac

#print axioms accepted
end AspisR1.PoolS2_PlannerCuts
