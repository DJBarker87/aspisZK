import PV_LIB_SliceNativeGraph
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceAllocNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_W5_LeafBoundary

def model_f62 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f62 H w prior stack

def law_f62 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f62 C e H w prior stack

theorem certified_f62 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f62 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f62 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f62 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f62 C e H w prior pre⟩
#print axioms certified_f62

def model_f46 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f46 H w prior stack

def law_f46 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f46 C e H w prior stack

theorem certified_f46 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f46 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f46 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f46 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f46 C e H w prior pre⟩
#print axioms certified_f46

def model_f36 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f36 H w prior stack

def law_f36 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f36 C e H w prior stack

theorem certified_f36 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f36 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f36 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f36 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f36 C e H w prior pre⟩
#print axioms certified_f36

def model_f37 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f37 H w prior stack

def law_f37 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f37 C e H w prior stack

theorem certified_f37 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f37 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f37 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f37 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f37 C e H w prior pre⟩
#print axioms certified_f37

def model_f38 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f38 H w prior stack

def law_f38 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f38 C e H w prior stack

theorem certified_f38 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f38 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f38 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f38 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f38 C e H w prior pre⟩
#print axioms certified_f38
end PV_LIB_SliceAllocNative
