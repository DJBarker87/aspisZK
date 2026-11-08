import PV_LIB_LeafObservation
import PV_W5_DropLeaf
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceDrop
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_W5_LeafBoundary

def model (C : Carrier OWNER Data) (e : Entry) (H : PV_W5_NativeFrame.Backend)
    (w : OWNER) (callee value : Data) (changes : Address → Option Data) :=
  PV_LIB.leafObserve (PV_W5_DropLeaf.call C e H w callee value changes)
def law (C : Carrier OWNER Data) (e : Entry) (H : PV_W5_NativeFrame.Backend)
    (w : OWNER) (callee value : Data) (changes : Address → Option Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) PV_RJ4IDB.NativeEvent) : Prop :=
  out = model C e H w callee value changes

theorem certified (C : Carrier OWNER Data) (e : Entry) (H : PV_W5_NativeFrame.Backend)
    (w : OWNER) (callee value : Data) (changes : Address → Option Data) (pre : Pre e w) :
    law C e H w callee value changes (PV_LIB.leafObserve (PV_W5_DropLeaf.call C e H w callee value changes)) ∧
    PV_W5_DropLeaf.Post C e H w callee value changes :=
  ⟨rfl,PV_W5_DropLeaf.contract C e H w callee value changes pre⟩
#print axioms certified
end PV_LIB_SliceDrop
