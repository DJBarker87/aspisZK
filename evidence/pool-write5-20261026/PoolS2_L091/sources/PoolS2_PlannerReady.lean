import PoolS2_NextValid
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerReady
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_Lanes PoolS2_PlannerModel

theorem ready (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (next : U64)
    (valid : PoolS2_MasterValidFacts.Valid m) (mask : m.initialized_lane_mask = 255#u8)
    (canonical : ∀ limb ∈ root.val, limb.val < 2147483647)
    (lanesValid : PoolS2_LaneFacts.Valid m.identity.pool 0 lanes.val)
    (chrono : PoolV_Chronology.chronology (Array.to_slice (sequences lanes))
      (Array.to_slice m.last_checkpoint_lane_sequences) m.has_checkpoint m.next_checkpoint_sequence = ok (0#u8,next)) :
    PoolS2_PlannerModel.run m lanes root bump = ok (.Ok (assembled m lanes root bump next)) := by
  classical
  have before := PoolS2_MasterValidExact.ready m valid
  have checked := (PoolS2_LaneFacts.accepted_iff m.identity.pool 0 lanes.val).mpr lanesValid
  have after := PoolS2_MasterValidExact.ready _ (PoolS2_NextValid.derived m lanes next valid lanesValid chrono)
  have after' : PoolS2_MasterValidation.run (assembled m lanes root bump next).next_master = ok (.Ok ()) := after
  simp [PoolS2_PlannerModel.run,before,mask,checked,chrono,after']
  exact canonical

#print axioms ready
end AspisR1.PoolS2_PlannerReady
