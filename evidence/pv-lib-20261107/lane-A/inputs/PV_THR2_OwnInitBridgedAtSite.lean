import PV_THR2_BoxDynRegistry14756
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitBridgedAtSite
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner PV_OWN2_Codec
/-- Exact source construction at14756, in the callback allocation's actual
world after14320 registration and arbitrary backend activity. Both registry
bindings, the physical data word and all payload words are DERIVED. Every14756
allocation outcome, complete world and event suffix is exactly the existing
allocation reply. No14756 success, shape, receiver, codec or adequacy premise.
This local theorem still requires the f361 own-entry join to reach this state. -/
theorem actual (callbackResources : Resources) (callbackEncode : Encode)
    (allocationStore sourceStore : Store Data) (w : OWNER) (handle data : Pointer)
    (a activation : Nat) (parents : List Frame) (backend : PV_STX_World.World)
    (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (answer : (callbackResources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok data.val)) (nonnull : data.val ≠ 0) :
    let allocated := (PV_THR2_ClosureBoxAllocation.reply callbackResources callbackEncode allocationStore w).world
    let c : Config := ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,sourceStore⟩
    let pre := withWorld (PV_THR2_BindingRegister.register c allocated) backend
    let payload := PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
      [PV_THR2_OwnInitPointerCodec.encode handle,
        PV_THR2_BoxDynRepresentationBridge.callback symbols (PV_THR2_PacketBoxBacking.root allocationStore)]
    PV_THR2_OwnInitSourceCodec.decodeBridged pre payload = some ⟨handle,data,symbols.vtable_115⟩ ∧
    PV_THR2_OwnInitAllocationHandlerBridged.handler resources encode fallback
      (.child PV_THR2_Source361InitChildren.fnAllocationFull activation [payload]) pre =
      PV_THR2_OwnInitAllocationReply.reply resources encode pre allocated.next
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)
        ⟨handle,data,symbols.vtable_115⟩ := by
  intro allocated c pre payload
  have binding := PV_THR2_BoxDynRegistry14756.registered_binding callbackResources callbackEncode
    allocationStore sourceStore w data a parents backend answer nonnull
  have decoded := PV_THR2_OwnInitSourceCodec.source pre symbols _ handle data binding
  have frame := PV_THR2_OwnUniformReceiverFrame.withWorld
    (PV_THR2_OwnUniformReceiverFrame.registered sourceStore a parents allocated).2 backend
  change PV_THR2_OwnUniformReceiverFrame.Frame a allocated.next
    (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) pre at frame
  change PV_THR2_OwnInitSourceCodec.decodeBridged pre payload = some ⟨handle,data,symbols.vtable_115⟩ at decoded
  have selected := PV_THR2_OwnInitAllocationSelection.selected frame
  refine ⟨decoded,?_⟩
  simp only [PV_THR2_OwnInitAllocationHandlerBridged.handler,ite_true,decoded,
    selected.1,frame.header]
#print axioms actual
end PV_THR2_OwnInitBridgedAtSite
