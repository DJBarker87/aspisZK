import PV_LIB_LeafObservation
import PV_W1_BoxEffects
set_option autoImplicit false
noncomputable section
namespace PV_LIB_BoxNew
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner R1Z.PV_FXM_ReserveWorld PV_W1_LeafBoundary
/-- CLOSED BoxNew's resource-indexed initialized-allocation function. The
source payload image and allocator encoding are the provider's arguments. -/
def model (resources : Resources) (encode : Encode) (e : Entry) (w : OWNER)
    (layout : PV_W1_BoxLeaf.Layout) (image : Nat → Option Nat) :=
  PV_LIB.leafObserve (e.store,PV_W1_BoxEffects.call resources encode e w layout image)
def law (resources : Resources) (encode : Encode) (e : Entry) (w : OWNER)
    (layout : PV_W1_BoxLeaf.Layout) (image : Nat → Option Nat)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) PV_RJ4IDB.NativeEvent) : Prop :=
  out = model resources encode e w layout image

theorem certified (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (e : Entry) (w : OWNER) (layout : PV_W1_BoxLeaf.Layout)
    (image : Nat → Option Nat) (events : List PV_RJ4IDB.NativeEvent)
    (pre : PV_W1_BoxEffects.Pre e w layout) :
    law resources encode e w layout image
      (PV_LIB.leafObserve (e.store,PV_W1_BoxEffects.call resources encode e w layout image)) ∧
    PV_W1_BoxEffects.Post C resources encode e w layout image events :=
  ⟨rfl,PV_W1_BoxEffects.contract C resources encode e w layout image events pre⟩
#print axioms certified
end PV_LIB_BoxNew
