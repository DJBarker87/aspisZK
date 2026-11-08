import PV_LIB_SliceNativeGraph
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceLoopNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_W5_LeafBoundary

def model_f20 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f20 H w prior stack

def law_f20 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f20 C e H w prior stack

theorem certified_f20 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f20 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f20 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f20 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f20 C e H w prior pre⟩
#print axioms certified_f20

def model_f16 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f16 H w prior stack

def law_f16 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f16 C e H w prior stack

theorem certified_f16 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f16 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f16 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f16 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f16 C e H w prior pre⟩
#print axioms certified_f16

def model_f17 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f17 H w prior stack

def law_f17 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f17 C e H w prior stack

theorem certified_f17 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f17 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f17 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f17 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f17 C e H w prior pre⟩
#print axioms certified_f17

def model_f18 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f18 H w prior stack

def law_f18 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f18 C e H w prior stack

theorem certified_f18 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f18 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f18 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f18 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f18 C e H w prior pre⟩
#print axioms certified_f18

def model_f10 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f10 H w prior stack

def law_f10 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_f10 C e H w prior stack

theorem certified_f10 (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_f10 C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_f10 H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_f10 H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.f10 C e H w prior pre⟩
#print axioms certified_f10
end PV_LIB_SliceLoopNative
