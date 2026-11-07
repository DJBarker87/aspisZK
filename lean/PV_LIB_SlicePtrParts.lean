import PV_LIB_LeafObservation
import PV_W5_PtrFromParts
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SlicePtrParts
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_W5_LeafBoundary

def modelMut (e : Entry) (w : OWNER) (pointer bytes : Nat) :=
  PV_LIB.leafObserve (e.store,(⟨.returned (.ok (PV_STX2_Source7QRuntimeValues.parts pointer bytes)),w,[]⟩ :
    Reply OWNER PV_RJ4IDB.NativeEvent Data))
def lawMut (e : Entry) (w : OWNER) (pointer bytes : Nat)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) PV_RJ4IDB.NativeEvent) : Prop :=
  out = modelMut e w pointer bytes

theorem certifiedMut (C : Carrier OWNER Data) (e : Entry) (H : PV_W5_NativeFrame.Backend)
    (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (pointer bytes : Nat) (pre : Pre e w) :
    lawMut e w pointer bytes (PV_LIB.leafObserve (e.store,
      PV_STX2_Source7QRuntimePartsReply.handler (PV_STX2_Source7QUniformResourceHandler.lift H)
        (.child PV_STX2_Source7QRuntimePartsCall.callee e.store.nextActivation [.number pointer,.number bytes]) w)) ∧
    PV_W5_PtrFromParts.MutPost C e H w prior pointer bytes := by
  have h := PV_W5_PtrFromParts.mut_contract C e H w prior pointer bytes pre
  refine ⟨?_,h⟩
  change PV_LIB.leafObserve _ = PV_LIB.leafObserve _
  rw [h.2]

def modelShared (e : Entry) (w : OWNER) (p : Address) (metadata : Data) :=
  PV_LIB.leafObserve (e.store,(⟨.returned (.ok (PV_STX2_TypedReferences.reference p metadata)),w,[]⟩ :
    Reply OWNER PV_RJ4IDB.NativeEvent Data))
def lawShared (e : Entry) (w : OWNER) (p : Address) (metadata : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) PV_RJ4IDB.NativeEvent) : Prop :=
  out = modelShared e w p metadata

theorem certifiedShared (C : Carrier OWNER Data) (e : Entry) (H : PV_W5_NativeFrame.Backend)
    (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (p : Address) (oldMetadata metadata : Data) (pre : Pre e w) :
    lawShared e w p metadata (PV_LIB.leafObserve (e.store,
      PV_STX2_SliceClonePointers.handler (PV_STX2_Source7QUniformResourceHandler.lift H)
        (.child PV_STX2_SliceClonePointers.callee e.store.nextActivation
          [PV_STX2_TypedReferences.reference p oldMetadata,metadata]) w)) ∧
    PV_W5_PtrFromParts.SharedPost C e H w prior p oldMetadata metadata := by
  have h := PV_W5_PtrFromParts.shared_contract C e H w prior p oldMetadata metadata pre
  refine ⟨?_,h⟩
  change PV_LIB.leafObserve _ = PV_LIB.leafObserve _
  rw [h.2]
#print axioms certifiedMut
#print axioms certifiedShared
end PV_LIB_SlicePtrParts
