import PoolS2_PlannerCuts
import PoolS2_ChronologyCodes
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerFacts
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_Lanes PoolS2_PlannerModel

theorem accepted (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (plan : Plan)
    (h : PoolS2_PlannerModel.run m lanes root bump = ok (.Ok plan)) :
    PoolS2_MasterValidFacts.Valid m ∧ m.initialized_lane_mask = 255#u8 ∧
    (∀ limb ∈ root.val, limb.val < 2147483647) ∧
    PoolS2_LaneFacts.Valid m.identity.pool 0 lanes.val ∧
    ∃ next : U64,
      PoolV_Chronology.chronology (Array.to_slice (sequences lanes))
        (Array.to_slice m.last_checkpoint_lane_sequences) m.has_checkpoint m.next_checkpoint_sequence = ok (0#u8,next) ∧
      PoolS2_MasterValidFacts.Valid (nextMaster m lanes next) ∧ plan = assembled m lanes root bump next := by
  obtain ⟨valid,mask,canonical,checked,pair,chrono,a,b,c,post,assembled⟩ :=
    PoolS2_PlannerCuts.accepted m lanes root bump plan h
  have code := PoolS2_ChronologyCodes.accepted_code _ _ _ _ pair chrono a b c
  have samePair : pair = (0#u8,pair.2) := Prod.ext code rfl
  refine ⟨PoolS2_MasterValidFacts.accepted m valid,mask,canonical,
    (PoolS2_LaneFacts.accepted_iff _ _ _).mp checked,pair.2,?_,?_,assembled⟩
  · exact chrono.trans (congrArg Result.ok samePair)
  · exact PoolS2_MasterValidFacts.accepted _ post

#print axioms accepted
end AspisR1.PoolS2_PlannerFacts
