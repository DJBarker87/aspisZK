import PoolS2_PlannerChronology
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerFirst
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_Lanes PoolS2_PlannerModel

theorem accepted (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (p : Plan)
    (h : run m lanes root bump = ok (.Ok p)) (first : m.has_checkpoint = false) :
    p.checkpoint.checkpoint_sequence = 0#u64 ∧
    p.next_master.next_checkpoint_sequence.val = 1 ∧
    m.last_checkpoint_lane_sequences = Array.repeat 8#usize 0#u64 := by
  have valid := ((PoolS2_PlannerExact.accepted_iff m lanes root bump p).mp h).1
  obtain ⟨_,_,_,_,_,_,_,initial⟩ := valid
  obtain ⟨seq,old⟩ := initial first
  have binding := (PoolS2_PlannerBindings.accepted m lanes root bump p h).2.2.2.2.1
  have increment := (PoolS2_PlannerChronology.increment m lanes root bump p h).2
  exact ⟨binding.trans seq,by simpa only [seq] using increment,old⟩

#print axioms accepted
end AspisR1.PoolS2_PlannerFirst
