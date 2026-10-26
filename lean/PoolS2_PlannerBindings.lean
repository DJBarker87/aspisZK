import PoolS2_PlannerExact
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerBindings
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_Lanes PoolS2_PlannerModel

theorem accepted (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (p : Plan)
    (h : run m lanes root bump = ok (.Ok p)) :
    p.checkpoint.bump = bump ∧ p.checkpoint.master = m.identity.pool ∧
    p.checkpoint.deployment_domain = m.identity.deployment_domain ∧
    p.checkpoint.global_root = root ∧ p.checkpoint.checkpoint_sequence = m.next_checkpoint_sequence ∧
    p.checkpoint.lane_sequences = sequences lanes ∧
    p.next_master.bump = m.bump ∧ p.next_master.identity = m.identity ∧
    p.next_master.verifier_policy = m.verifier_policy ∧
    p.next_master.initialized_lane_mask = m.initialized_lane_mask ∧
    p.next_master.has_checkpoint = true ∧ p.next_master.last_checkpoint_lane_sequences = sequences lanes := by
  obtain ⟨_,_,_,_,next,_,same⟩ := (PoolS2_PlannerExact.accepted_iff m lanes root bump p).mp h
  subst p
  simp [assembled,nextMaster]

#print axioms accepted
end AspisR1.PoolS2_PlannerBindings
