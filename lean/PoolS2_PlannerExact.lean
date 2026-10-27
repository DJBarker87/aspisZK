import PoolS2_PlannerFacts
import PoolS2_PlannerReady
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerExact
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_Lanes PoolS2_PlannerModel

/-- Exact acceptance for the explicitly named full pure REFERENCE.
No native source refinement is asserted by this theorem. Post-validation is
proved, not retained as a condition. Full original input structs are arbitrary. -/
theorem accepted_iff (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (plan : Plan) :
    PoolS2_PlannerModel.run m lanes root bump = ok (.Ok plan) ↔
    PoolS2_MasterValidFacts.Valid m ∧ m.initialized_lane_mask = 255#u8 ∧
    (∀ limb ∈ root.val, limb.val < 2147483647) ∧
    PoolS2_LaneFacts.Valid m.identity.pool 0 lanes.val ∧
    ∃ next : U64,
      PoolV_Chronology.chronology (Array.to_slice (sequences lanes))
        (Array.to_slice m.last_checkpoint_lane_sequences) m.has_checkpoint m.next_checkpoint_sequence = ok (0#u8,next) ∧
      plan = assembled m lanes root bump next := by
  constructor
  · intro h
    obtain ⟨valid,mask,canonical,checked,next,chrono,_,same⟩ := PoolS2_PlannerFacts.accepted m lanes root bump plan h
    exact ⟨valid,mask,canonical,checked,next,chrono,same⟩
  · rintro ⟨valid,mask,canonical,checked,next,chrono,same⟩
    subst plan
    exact PoolS2_PlannerReady.ready m lanes root bump next valid mask canonical checked chrono

#print axioms accepted_iff
end AspisR1.PoolS2_PlannerExact
