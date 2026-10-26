import PoolS2_PlannerBindings
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerChronology
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_Lanes PoolS2_PlannerModel

theorem increment (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (p : Plan)
    (h : run m lanes root bump = ok (.Ok p)) :
    m.next_checkpoint_sequence.val < U64.max ∧
    p.next_master.next_checkpoint_sequence.val = m.next_checkpoint_sequence.val+1 := by
  obtain ⟨_,_,_,_,next,chrono,same⟩ := (PoolS2_PlannerExact.accepted_iff m lanes root bump p).mp h
  have facts := PoolV_ChronologyAccepted.accepted_sequence _ _ _ _ _ chrono
  subst p
  exact facts

theorem repeated (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (p : Plan)
    (h : run m lanes root bump = ok (.Ok p)) (has : m.has_checkpoint = true) :
    (∀ a b : U64, (a,b) ∈ (sequences lanes).val.zip m.last_checkpoint_lane_sequences.val → b.val ≤ a.val) ∧
    (∃ a b : U64, (a,b) ∈ (sequences lanes).val.zip m.last_checkpoint_lane_sequences.val ∧ b.val < a.val) := by
  obtain ⟨_,_,_,_,next,chrono,_⟩ := (PoolS2_PlannerExact.accepted_iff m lanes root bump p).mp h
  rw [has] at chrono
  exact PoolV_ChronologyAccepted.repeated _ _ _ _ chrono

#print axioms increment
#print axioms repeated
end AspisR1.PoolS2_PlannerChronology
