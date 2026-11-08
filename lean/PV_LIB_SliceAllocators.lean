import PV_LIB_LeafObservation
import PV_W5_AllocatorContracts
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceAllocators
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_EVHB_RawVecOwner PV_W5_LeafBoundary

def model65 (resources : Resources) (encode : Encode) (e : Entry) (w : OWNER) (bytes : Nat) :=
  PV_LIB.leafObserve (e.store,PV_W5_MallocContract.reply resources encode e.parents w bytes)
def law65 (resources : Resources) (encode : Encode) (e : Entry) (w : OWNER) (bytes : Nat)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) PV_RJ4IDB.NativeEvent) : Prop :=
  out = model65 resources encode e w bytes

theorem certified65 (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (e : Entry) (w : OWNER) (bytes : Nat) (prior : List PV_RJ4IDB.NativeEvent)
    (pre : PV_W5_MallocOwned.Pre e w bytes)
    (semantics : PV_STX2_IntrinsicSemantics_Malloc resources) :
    law65 resources encode e w bytes
      (PV_LIB.leafObserve (e.store,PV_W5_MallocContract.reply resources encode e.parents w bytes)) ∧
    PV_W5_AllocatorContracts.MallocPost C resources encode e w bytes prior :=
  ⟨rfl,PV_W5_AllocatorContracts.malloc C resources encode e w bytes prior pre semantics⟩

def model64 (resources : Resources) (encode : Encode) (e : Entry) (w : OWNER) (bytes : Nat) :=
  PV_LIB.leafObserve (e.store,PV_W5_ZeroedLeaf.reply resources encode e w bytes)
def law64 (resources : Resources) (encode : Encode) (e : Entry) (w : OWNER) (bytes : Nat)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) PV_RJ4IDB.NativeEvent) : Prop :=
  out = model64 resources encode e w bytes

theorem certified64 (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (e : Entry) (w : OWNER) (bytes : Nat) (prior : List PV_RJ4IDB.NativeEvent)
    (pre : PV_W5_MallocOwned.Pre e w bytes)
    (semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources) :
    law64 resources encode e w bytes
      (PV_LIB.leafObserve (e.store,PV_W5_ZeroedLeaf.reply resources encode e w bytes)) ∧
    PV_W5_AllocatorContracts.ZeroedPost C resources encode e w bytes prior :=
  ⟨rfl,PV_W5_AllocatorContracts.zeroed C resources encode e w bytes prior pre semantics⟩
#print axioms certified65
#print axioms certified64
end PV_LIB_SliceAllocators
