import PV_LIB_SPEC_ActiveHistory16020
import PV_LIB_SPEC_Active278Issue20
import PV_LIB_SPEC_HistoryExtend20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveHistory16520
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def store160 : Store Data := PV_LIB_SPEC_Active27720.stored
  PV_LIB_SPEC_ActiveDelivery20.stored activation PV_LIB_SPEC_Entry13.slot.source

theorem state160 (e : Entry) (a : Nat) :
    (history e a 160).state =
      (stage store160 activation parents (PV_THR2_F170.live.body.drop 17) e.world [] [] []).state := by
  rw [PV_LIB_SPEC_ActiveHistory16020.original160]
  rfl

def at164 (e : Entry) (a : Nat) : Execution :=
  PV_LIB_SPEC_Active27820.before store160 activation parents PV_LIB_SPEC_Entry13.slot.source e.world []
    (history e a 160).issued (history e a 160).consumed

theorem original164 (e : Entry) (a : Nat) : history e a 164 = at164 e a := by
  apply PV_LIB_SPEC_HistoryExtend20.full e a 160 4
    (stage store160 activation parents (PV_THR2_F170.live.body.drop 17) e.world [] [] []).state
    (fun issued consumed => PV_LIB_SPEC_Active27820.before store160 activation parents
      PV_LIB_SPEC_Entry13.slot.source e.world [] issued consumed) (state160 e a)
  intro issued consumed
  exact PV_LIB_SPEC_Active278Issue20.run _ _ (fun _ w => ⟨.pending,w,[]⟩)
    store160 activation parents PV_LIB_SPEC_Entry13.slot.source e.world [] issued consumed
    (write_same _ _ _)

theorem original165 (e : Entry) (a : Nat) :
    history e a 165 =
      ⟨PV_LIB_SPEC_Active27820.out store160 activation parents PV_LIB_SPEC_Entry13.slot.source e.world [],
        (at164 e a).issued,
        PV_LIB_SPEC_Active27820.origin store160 activation PV_LIB_SPEC_Entry13.slot.source
          (history e a 160).consumed :: (history e a 160).consumed⟩ := by
  change PV_LIB_A_ActiveEnvironment17.run _ _ (164+1) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.step _ _ (history e a 164) = _
  rw [original164]
  exact PV_LIB_SPEC_Active27820.consume _ store160 activation parents PV_LIB_SPEC_Entry13.slot.source
    e.world [] _ _

#print axioms store160
#print axioms state160
#print axioms at164
#print axioms original164
#print axioms original165
end PV_LIB_SPEC_ActiveHistory16520
