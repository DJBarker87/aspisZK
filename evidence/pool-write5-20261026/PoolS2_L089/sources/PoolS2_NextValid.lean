import PoolS2_PlannerModel
set_option autoImplicit false
namespace AspisR1.PoolS2_NextValid
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_Lanes PoolS2_PlannerModel

theorem derived (m : Master) (lanes : Lanes) (next : U64)
    (valid : PoolS2_MasterValidFacts.Valid m)
    (lanesValid : PoolS2_LaneFacts.Valid m.identity.pool 0 lanes.val)
    (chrono : PoolV_Chronology.chronology (Array.to_slice (sequences lanes))
      (Array.to_slice m.last_checkpoint_lane_sequences) m.has_checkpoint m.next_checkpoint_sequence = ok (0#u8,next)) :
    PoolS2_MasterValidFacts.Valid (nextMaster m lanes next) := by
  rcases valid with ⟨pool,mint,token,domain,policy,_,_,_⟩
  have laneBounds := PoolS2_LaneFacts.bounds m.identity.pool 0 lanes.val lanesValid
  have increment := (PoolV_ChronologyAccepted.accepted_sequence _ _ _ _ _ chrono).2
  have nonzero : next ≠ 0#u64 := by
    intro zero
    have eq := congrArg UScalar.val zero
    scalar_tac
  refine ⟨pool,mint,token,domain,policy,?_,?_,?_⟩
  · simpa [nextMaster,sequences] using laneBounds
  · simpa [nextMaster] using nonzero
  · simp [nextMaster]

#print axioms derived
end AspisR1.PoolS2_NextValid
