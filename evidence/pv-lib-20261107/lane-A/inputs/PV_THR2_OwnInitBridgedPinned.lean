import PV_THR2_OwnInitBridgedAtSite
import PV_THR2_BoxDynBinaryLayout
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitBridgedPinned
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner PV_OWN2_Codec
/-- Pinned binary-structural symbols are INSTALLED from the existing checked
address table. No vtable/linkage hypothesis occurs at a run. The source and
binary interpretation adequacy obligation remains named and unassumed. -/
theorem actual14756 (callbackResources : Resources) (callbackEncode : Encode)
    (allocationStore sourceStore : Store Data) (w : OWNER) (handle data : Pointer)
    (a activation : Nat) (parents : List Frame) (backend : PV_STX_World.World)
    (loadBias : Pointer) (siteIndex : Fin 11) (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (answer : (callbackResources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok data.val)) (nonnull : data.val ≠ 0) :
    let allocated := (PV_THR2_ClosureBoxAllocation.reply callbackResources callbackEncode allocationStore w).world
    let c : Config := ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,sourceStore⟩
    let pre := withWorld (PV_THR2_BindingRegister.register c allocated) backend
    let payload := PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
      [PV_THR2_OwnInitPointerCodec.encode handle,
        PV_THR2_BoxDynRepresentationBridge.callback (PV_THR2_BoxDynBinaryLayout.symbols loadBias siteIndex)
          (PV_THR2_PacketBoxBacking.root allocationStore)]
    PV_THR2_OwnInitSourceCodec.decodeBridged pre payload =
      some ⟨handle,data,PV_THR2_BoxDynBinaryLayout.runtimeAddress loadBias siteIndex⟩ ∧
    PV_THR2_OwnInitAllocationHandlerBridged.handler resources encode fallback
      (.child PV_THR2_Source361InitChildren.fnAllocationFull activation [payload]) pre =
      PV_THR2_OwnInitAllocationReply.reply resources encode pre allocated.next
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)
        ⟨handle,data,PV_THR2_BoxDynBinaryLayout.runtimeAddress loadBias siteIndex⟩ :=
  PV_THR2_OwnInitBridgedAtSite.actual callbackResources callbackEncode allocationStore sourceStore
    w handle data a activation parents backend (PV_THR2_BoxDynBinaryLayout.symbols loadBias siteIndex)
    resources encode fallback answer nonnull
#print axioms actual14756
end PV_THR2_OwnInitBridgedPinned
