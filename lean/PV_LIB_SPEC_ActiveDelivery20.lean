import PV_LIB_SPEC_ActivePoll20
import PV_LIB_SPEC_NativeDelivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveDelivery20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_SPEC_ActivePoll20 (config wait request store)
open PV_LIB_A_ActiveGetter17 (store154 token)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_TlsNative15 (reference)

def stored : Store Data := write (write store ⟨store154.nextActivation,0,[]⟩
  (some reference)) ⟨activation,7,[]⟩ (some reference)
def after (e : Entry) : State :=
  ⟨⟨.running ⟨{activation := activation,remaining := PV_THR2_F170.live.body.drop 14},parents,stored⟩,e.world,[]⟩,[]⟩

theorem transition (e : Entry) (a : Nat) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
      (PV_LIB_A_ActiveTlsNative17.parameters resources) config
      ⟨⟨.running config,e.world,[]⟩,[]⟩ = after e := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  have table : PV_LIB_StoreActionTable.v2 token = none := rfl
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running config,e.world,[]⟩,[]⟩ := by
    simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,config,wait,request,PV_THR2_OwnInitAction.selected,
      PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
      PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node14,lookup,table]
  rw [PV_LIB_SPEC_NativeDelivery16.full _ _ config e.world [] [] wait token
    store154.nextActivation 7 [PV_LIB_A_ActiveGetter17.init] quiet (by rfl) rfl rfl rfl rfl lookup]
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show wait.request=request from rfl,
    PV_LIB_SPEC_ActivePoll20.answer e a resources,Option.getD_some]
  rfl

#print axioms stored
#print axioms after
#print axioms transition
end PV_LIB_SPEC_ActiveDelivery20
