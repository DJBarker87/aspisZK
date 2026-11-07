import PV_LIB_SliceNativeGraph
import PV_W5_NoAllocShim
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceNoAlloc
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER PV_W5_LeafBoundary

def model (C : Carrier OWNER Data) (e : Entry) (external : PV_W5_NoAllocShim.External)
    (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C (PV_W5_NoAllocShim.entry e)
    PV_STX2_Source7QRuntimePrelude.callee (PV_W5_NoAllocShim.backend external) w prior stack
def law (C : Carrier OWNER Data) (e : Entry) (external : PV_W5_NoAllocShim.External)
    (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop := out = model C e external w prior stack

theorem certified (C : Carrier OWNER Data) (e : Entry) (external : PV_W5_NoAllocShim.External)
    (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) (pre : Pre e w) :
    law C e external w prior stack (PV_LIB_SliceNativeGraph.model C (PV_W5_NoAllocShim.entry e)
      PV_STX2_Source7QRuntimePrelude.callee (PV_W5_NoAllocShim.backend external) w prior stack) ∧
    PV_W5_NoAllocShim.Post C e external w prior :=
  ⟨rfl,PV_W5_NoAllocShim.contract C e external w prior pre⟩
#print axioms certified
end PV_LIB_SliceNoAlloc
