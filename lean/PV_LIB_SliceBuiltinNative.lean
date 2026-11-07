import PV_LIB_SliceNativeGraph
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceBuiltinNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_W5_LeafBoundary

def model_arrayRepeat (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_arrayRepeat H w prior stack

def law_arrayRepeat (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_arrayRepeat C e H w prior stack

theorem certified_arrayRepeat (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_arrayRepeat C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_arrayRepeat H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_arrayRepeat H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.arrayRepeat C e H w prior pre⟩
#print axioms certified_arrayRepeat

def model_arrayToSliceMut (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_arrayToSliceMut H w prior stack

def law_arrayToSliceMut (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_arrayToSliceMut C e H w prior stack

theorem certified_arrayToSliceMut (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_arrayToSliceMut C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_arrayToSliceMut H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_arrayToSliceMut H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.arrayToSliceMut C e H w prior pre⟩
#print axioms certified_arrayToSliceMut

def model_arrayToSliceShared (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_arrayToSliceShared H w prior stack

def law_arrayToSliceShared (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_arrayToSliceShared C e H w prior stack

theorem certified_arrayToSliceShared (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_arrayToSliceShared C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_arrayToSliceShared H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_arrayToSliceShared H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.arrayToSliceShared C e H w prior pre⟩
#print axioms certified_arrayToSliceShared

def model_indexMut (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_indexMut H w prior stack

def law_indexMut (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_indexMut C e H w prior stack

theorem certified_indexMut (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_indexMut C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_indexMut H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_indexMut H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.indexMut C e H w prior pre⟩
#print axioms certified_indexMut
end PV_LIB_SliceBuiltinNative
