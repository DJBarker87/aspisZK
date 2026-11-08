import PV_LIB_SPEC_ActiveHistory16520
import PV_LIB_SPEC_Active279Issue20
import PV_LIB_SPEC_HistoryExtend20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveHistory16920
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def store165 : Store Data := PV_LIB_SPEC_Active27820.stored
  PV_LIB_SPEC_ActiveHistory16520.store160 activation PV_LIB_SPEC_Entry13.slot.source

theorem state165 (e : Entry) (a : Nat) :
    (history e a 165).state =
      (stage store165 activation parents (PV_THR2_F170.live.body.drop 21) e.world [] [] []).state := by
  rw [PV_LIB_SPEC_ActiveHistory16520.original165]
  rfl

def at168 (e : Entry) (a : Nat) : Execution :=
  PV_LIB_SPEC_Active27920.before store165 activation parents PV_LIB_SPEC_Entry13.slot.source e.world []
    (history e a 165).issued (history e a 165).consumed

theorem original168 (e : Entry) (a : Nat) : history e a 168 = at168 e a := by
  apply PV_LIB_SPEC_HistoryExtend20.full e a 165 3
    (stage store165 activation parents (PV_THR2_F170.live.body.drop 21) e.world [] [] []).state
    (fun issued consumed => PV_LIB_SPEC_Active27920.before store165 activation parents
      PV_LIB_SPEC_Entry13.slot.source e.world [] issued consumed) (state165 e a)
  intro issued consumed
  exact PV_LIB_SPEC_Active279Issue20.run _ _ (fun _ w => ⟨.pending,w,[]⟩)
    store165 activation parents PV_LIB_SPEC_Entry13.slot.source e.world [] issued consumed
    (write_same _ _ _)

theorem original169 (e : Entry) (a : Nat) :
    history e a 169 =
      ⟨PV_LIB_SPEC_Active27920.out store165 activation parents PV_LIB_SPEC_Entry13.slot.source e.world [],
        (at168 e a).issued,
        PV_LIB_SPEC_Active27920.origin store165 activation PV_LIB_SPEC_Entry13.slot.source
          (history e a 165).consumed :: (history e a 165).consumed⟩ := by
  change PV_LIB_A_ActiveEnvironment17.run _ _ (168+1) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.step _ _ (history e a 168) = _
  rw [original168]
  exact PV_LIB_SPEC_Active27920.consume _ store165 activation parents PV_LIB_SPEC_Entry13.slot.source
    e.world [] _ _

#print axioms store165
#print axioms state165
#print axioms at168
#print axioms original168
#print axioms original169
end PV_LIB_SPEC_ActiveHistory16920
