import PV_THR2_OwnInitAllocationHandler
import PV_THR2_OwnInitAllocationCases
import PV_THR2_SourceOwnership
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitHandlerCases
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on owner acceptance of amended translator. Hypothesis:
FreshAllocationValidity' at the actual generated local45 binding's pre-state.
The exact allocation function token, operand codec, source-derived descriptor,
full resource reply and field-store ownership compose BY NAME. No receiver,
endpoint premise or fixed successful child reply is supplied. Original-entry
transport, actual argument association and SourceInitBoxOwnership join are open;
this theorem is a local handler case and is NOT OwnInit closure. -/
theorem allocation (C : Carrier OWNER Data) (store : Store Data) (a : Nat)
    (parents : List Frame) (s : OWNER) (resources : Resources) (encode : Encode)
    (granted : GrantedRegions) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (activation : Nat)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (valid : FreshAllocationValidity' resources granted
      (PV_THR2_BindingRegister.register
        ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,store⟩ s)) :
    let c := Config.mk {activation := a,remaining := PV_THR2_F361.live.body.drop 113} parents store
    let pre := PV_THR2_BindingRegister.register c s
    PV_THR2_OwnInitAllocationCases.Outcome ⟨a,[45]⟩ words
      (resources (.malloc 24) (world s)).answer
      (PV_THR2_OwnInitAllocationHandler.handler resources encode fallback
        (.child PV_THR2_Source361InitChildren.fnAllocationFull activation
          [PV_THR2_OwnInitFieldCodec.init words.handle words.data words.vtable]) pre) := by
  have frame := PV_THR2_OwnUniformReceiverFrame.registered store a parents s
  dsimp only
  rw [PV_THR2_OwnInitAllocationHandler.at_site resources encode fallback activation
    words.handle words.data words.vtable frame.2]
  exact PV_THR2_OwnInitAllocationCases.all C store a parents s resources encode granted words valid
#print axioms allocation
end PV_THR2_OwnInitHandlerCases
