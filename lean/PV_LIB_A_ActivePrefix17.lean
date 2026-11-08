import PV_LIB_A_ActiveEnvironment17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActivePrefix17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_A_ActiveEnvironment17

def history (e : PV_LIB_SPEC_EntryWorld18.Entry) (a n : Nat) : Execution :=
  run (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
    PV_LIB_SPEC_ReachedEnvironment14.parameters n
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))

theorem body141 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    PV_LIB_SPEC_LaneAJoins18.BodyEntry (PV_LIB_SPEC_LaneAJoins18.history e a 141)
      PV_THR2_F170.live.body := by
  refine ⟨⟨{activation := PV_LIB_A_F5FullEntry16.activation,remaining := PV_THR2_F170.live.body},
    PV_LIB_A_F5FullEntry16.parents,PV_LIB_A_F5FullEntry16.store⟩,?_,rfl,rfl,rfl,rfl⟩
  rw [PV_LIB_A_F5FullEntry16.original141]
  rfl

/-- The old trap itself proves that the corrected callback cannot have been
polled on ANY earlier prefix: otherwise old141 could not be a fresh BODY entry.
This avoids replay/unrolling of the retained prefix. -/
theorem prefix_away (e : PV_LIB_SPEC_EntryWorld18.Entry) (a k : Nat) (bound : k ≤ 141) :
    ¬Corrected (PV_LIB_SPEC_LaneAJoins18.history e a k).state := by
  rintro ⟨s,act,parents,pointer,w,events,eq⟩
  let q := PV_LIB_SPEC_LaneAJoins18.history e a k
  have hq : q = ⟨PV_LIB_A_F5CallbackTrap16.waiting s act parents pointer w events,q.issued,q.consumed⟩ :=
    PV_LIB_A_F170Return16.execution_ext _ _ eq rfl rfl
  have noEntry := PV_LIB_A_F5CallbackTrap16.no_body_entry
    (PV_LIB_SPEC_EntryWorld18.frame e a) s act parents pointer w events q.issued q.consumed
    (141-k) PV_THR2_F170.live.body
  have reached := body141 e a
  change PV_LIB_SPEC_LaneAJoins18.BodyEntry
    (PV_LIB_SPEC_ReachedNative14.run _ _ 141 _) _ at reached
  rw [show 141=k+(141-k) from (Nat.add_sub_of_le bound).symm,PV_LIB_SPEC_Original14.run_add] at reached
  change PV_LIB_SPEC_LaneAJoins18.BodyEntry (PV_LIB_SPEC_ReachedNative14.run _ _ (141-k) q) _ at reached
  rw [hq] at reached
  exact noEntry reached

theorem preserved (e : PV_LIB_SPEC_EntryWorld18.Entry) (a n : Nat) (bound : n ≤ 141) :
    history e a n = PV_LIB_SPEC_LaneAJoins18.history e a n := by
  apply transport
  intro k hk
  exact prefix_away e a k (Nat.le_trans (Nat.le_of_lt hk) bound)

theorem original85 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    history e a 85 = PV_LIB_SPEC_World18_Tls85Data16.at85 e := by
  rw [preserved e a 85 (by decide)]
  exact PV_LIB_SPEC_LaneAJoins18.original85 e a

theorem original141 (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    (history e a 141).state = PV_LIB_A_F5FullEntry16.at141 e := by
  rw [preserved e a 141 (by decide)]
  exact PV_LIB_A_F5FullEntry16.original141 e a

#print axioms history
#print axioms body141
#print axioms prefix_away
#print axioms preserved
#print axioms original85
#print axioms original141
end PV_LIB_A_ActivePrefix17
